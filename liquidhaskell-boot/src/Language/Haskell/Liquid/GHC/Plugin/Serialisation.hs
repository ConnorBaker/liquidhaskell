{-# LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.Liquid.GHC.Plugin.Serialisation (
      -- * Serialising and deserialising things from/to specs.
        serialiseLiquidLib
      , deserialiseLiquidLib

      ) where

import qualified Data.Array                               as Array
import qualified Data.Binary                             as B
import qualified Data.Binary.Builder                     as Builder
import qualified Data.Binary.Put                         as B
import qualified Data.ByteString.Lazy                    as B
import qualified Data.ByteString                         as Strict
import           Data.Data (Data)
import           Control.Exception
import           Control.Exception.Backtrace
import           Control.Exception.Context
import           Data.Generics (ext0, gmapAccumT)
import           Data.HashMap.Strict                     as M
import           Data.Typeable                            ( typeOf )
import           Data.Word                               (Word8)
import           GHC.Stack (HasCallStack)
import           GHC.Data.Maybe (MaybeErr (..))
import           GHC.Iface.Load (findAndReadIface)
import           GHC.Iface.Syntax (ifAnnotatedTarget)
import           GHC.Unit.Module (getModuleInstantiation)
import           GHC.Unit.Module.ModIface (ModIface)
import qualified GHC.Unit.Home.Graph as HUG
import           GHC.Driver.Env (hsc_HUG)

import qualified Liquid.GHC.API as GHC
import           Language.Haskell.Liquid.GHC.Plugin.Types (LiquidLib)
import           Language.Haskell.Liquid.Types.Names
import qualified Language.Haskell.Liquid.GHC.Plugin.AnnotationCodec as Codec
import qualified Language.Haskell.Liquid.GHC.Plugin.AnnotationIdentity as Identity


--
-- Serialising and deserialising Specs
--

getLiquidLibBytesFromEPS
  :: GHC.HscEnv
  -> GHC.Module
  -> GHC.ExternalPackageState
  -> IO (Maybe LiquidLibBytes)
getLiquidLibBytesFromEPS env thisModule eps =
    case GHC.findAnns LiquidLibBytes (GHC.eps_ann_env eps) (GHC.ModuleTarget thisModule) of
      [payload] -> pure (Just payload)
      [] -> do
        -- EPS deliberately discards raw annotations from its cached interfaces.
        -- Audit a typed lookup miss against the checked on-disk interface so an
        -- annotation from an obsolete compiler unit cannot masquerade as absent.
        result <- findAndReadIface env (GHC.text "LiquidHaskell annotation identity")
          (fst $ getModuleInstantiation thisModule) thisModule GHC.NotBoot
        case result of
          Succeeded (iface, _) -> getIfacePayload iface
          Failed _ -> ioError $ userError $
            "LiquidHaskell cannot audit annotations for "
            ++ GHC.showSDocUnsafe (GHC.ppr thisModule)
            ++ "; rebuild the dependency with the current compiler."
      _ -> identityFailure Identity.DuplicateAnnotations

getLiquidLibBytes :: GHC.HscEnv
                        -> GHC.Module
                        -> GHC.ExternalPackageState
                        -> IO (Maybe LiquidLibBytes)
getLiquidLibBytes env thisModule eps = do
    mb_modInfo <- HUG.lookupHugByModule thisModule (hsc_HUG env)
    case mb_modInfo of
      Just modInfo | thisModule == GHC.mi_module (GHC.hm_iface modInfo) ->
        getIfacePayload (GHC.hm_iface modInfo)
      _ -> getLiquidLibBytesFromEPS env thisModule eps

getIfacePayload :: ModIface -> IO (Maybe LiquidLibBytes)
getIfacePayload iface =
    case Identity.selectAnnotationPayload (typeOf $ LiquidLibBytes []) payloads of
      Left err -> identityFailure err
      Right bytes -> pure (LiquidLibBytes <$> bytes)
  where
    payloads = [ GHC.ifAnnotatedValue annotation
               | annotation <- GHC.mi_anns iface
               , GHC.ModuleTarget _ <- [ifAnnotatedTarget annotation]
               ]

identityFailure :: Identity.AnnotationIdentityError -> IO a
identityFailure = ioError . userError . Identity.annotationIdentityError

newtype LiquidLibBytes = LiquidLibBytes { unLiquidLibBytes :: [Word8] }

-- | Serialise the complete 'LiquidLib' and its resolved-name table into a
-- losslessly compressed annotation payload.
serialiseLiquidLib :: LiquidLib -> GHC.Module -> IO GHC.Annotation
serialiseLiquidLib lib thisModule = do
    bs <- encodeLiquidLib lib
    -- Force the compact encoding before returning an annotation thunk. Otherwise
    -- the boxed-byte payload can retain the whole transformed specification.
    payload <- evaluate $ Codec.encodePayload (B.toStrict bs)
    return $ GHC.Annotation
      (GHC.ModuleTarget thisModule)
      (GHC.toSerialized unLiquidLibBytes (LiquidLibBytes $ Strict.unpack payload))

deserialiseLiquidLib
  :: GHC.HscEnv
  -> GHC.Module
  -> GHC.ExternalPackageState
  -> GHC.NameCache
  -> IO (Maybe LiquidLib)
deserialiseLiquidLib env thisModule eps nameCache = do
    mlibbs <- getLiquidLibBytes env thisModule eps
    case mlibbs of
      Just (LiquidLibBytes ws) -> do
        bs <- decodePayload ws
        Just <$> decodeLiquidLib nameCache bs
      _ -> return Nothing

decodePayload :: [Word8] -> IO B.ByteString
decodePayload ws = case Codec.decodePayload (Strict.pack ws) of
    Left message -> ioError (userError message)
    Right bytes -> pure (B.fromStrict bytes)

encodeLiquidLib :: LiquidLib -> IO B.ByteString
encodeLiquidLib lib0 = rethrowWithCallStackIO $ do
    let (lib1, ns) = collectLHNames lib0
    bh <- GHC.openBinMem (1024*1024)
    GHC.putWithUserData GHC.QuietBinIFace GHC.SafeExtraCompression bh ns
    GHC.withBinBuffer bh $ \bs ->
      return $ Builder.toLazyByteString $ B.execPut (B.put lib1) <> Builder.fromByteString bs

decodeLiquidLib :: GHC.NameCache -> B.ByteString -> IO LiquidLib
decodeLiquidLib nameCache bs0 = rethrowWithCallStackIO $ do
    case B.decodeOrFail bs0 of
      Left (_, _, err) -> error $ "decodeLiquidLib: decodeOrFail: " ++ err
      Right (bs1, _, lib) -> do
        bh <- GHC.unsafeUnpackBinBuffer $ B.toStrict bs1
        ns <- GHC.getWithUserData nameCache bh
        let n = fromIntegral $ length ns
            arr = Array.listArray (0, n - 1) ns
        return $ mapLHNames (resolveLHNameIndex arr) lib
  where
    resolveLHNameIndex :: Array.Array Word LHResolvedName -> LHName -> LHName
    resolveLHNameIndex arr lhname =
      case getLHNameResolved lhname of
        LHRIndex i ->
          if i <= snd (Array.bounds arr) then
            makeResolvedLHName (arr Array.! i) (getLHNameSymbol lhname)
          else
            error $ "decodeLiquidLib: index out of bounds: " ++ show (i, Array.bounds arr)
        _ ->
          lhname

newtype AccF a b = AccF { unAccF :: a -> b -> (a, b) }

collectLHNames :: Data a => a -> (a, [LHResolvedName])
collectLHNames t =
    let ((_, _, xs), t') = go (0, M.empty, []) t
     in (t', reverse xs)
  where
    go
      :: Data a
      => (Word, M.HashMap LHResolvedName Word, [LHResolvedName])
      -> a
      -> ((Word, M.HashMap LHResolvedName Word, [LHResolvedName]), a)
    go = gmapAccumT $ unAccF $ AccF go `ext0` AccF collectName

    collectName acc@(sz, m, xs) n = case M.lookup n m of
      Just i -> (acc, LHRIndex i)
      Nothing -> ((sz + 1, M.insert n sz m, n : xs), LHRIndex sz)

-- | Rethrow an exception so we have an indication of where it was thrown in
-- the stack trace.
rethrowWithCallStackIO :: HasCallStack => IO a -> IO a
rethrowWithCallStackIO action = catchNoPropagate action $ \(ExceptionWithContext ctx (e :: SomeException)) -> do
    btAnn <- collectBacktraces
    rethrowIO $ ExceptionWithContext (addExceptionAnnotation btAnn ctx) e
