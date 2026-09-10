#!/usr/bin/env bash
# Run inside the built compiler's environment, e.g.
# cabal exec -- bash scripts/test/test_totality_policy.sh
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/../.." && pwd)
policy_tmp=$(mktemp -d "${TMPDIR:-/tmp}/lh-totality-policy.XXXXXX")
client="$repo_root/tests/totality-policy/PolicyClient.hs"
common=(-O2 -fforce-recomp -XGHC2024 -outputdir "$policy_tmp/out")
boot=(-hide-package liquidhaskell -plugin-package liquidhaskell-boot -fplugin=LiquidHaskellBoot -fplugin-opt=LiquidHaskellBoot:--no-annotations)

expect_error() {
  local label=$1 needle=$2
  shift 2
  if "$@" > "$policy_tmp/$label.log" 2>&1; then
    echo "$label: unexpectedly accepted" >&2
    exit 1
  fi
  if ! grep -Fq "$needle" "$policy_tmp/$label.log"; then
    echo "$label: wrong diagnostic; see $policy_tmp/$label.log" >&2
    exit 1
  fi
}

expect_error missing-policy "LiquidHaskell totality policy is unavailable" \
  ghc "${common[@]}" "${boot[@]}" -fplugin-opt=LiquidHaskellBoot:--total-Haskell -c "$client"

# Expose a package with the right module but no LH annotation. A successful
# interface lookup is insufficient: the selected policy must actually exist.
ghc "${common[@]}" -fclear-plugins -this-unit-id liquidhaskell-empty-policy \
  -outputdir "$policy_tmp/fake" -c "$repo_root/tests/totality-policy/EmptyPolicy.hs"
ghc-pkg init "$policy_tmp/package.conf.d"
base_unit=$(ghc-pkg field base id --simple-output)
ghc-pkg --package-db "$policy_tmp/package.conf.d" register - <<EOF
name: liquidhaskell
version: 0.0.0
id: liquidhaskell-empty-policy
key: liquidhaskell-empty-policy
exposed: True
exposed-modules: Liquid.Prelude.Totality_LHAssumptions
import-dirs: $policy_tmp/fake
depends: $base_unit
EOF
expect_error missing-annotation "LiquidHaskell totality policy is unavailable" \
  ghc "${common[@]}" "${boot[@]}" -package-db "$policy_tmp/package.conf.d" \
  -hide-all-packages -package base -package ghc-prim -package-id liquidhaskell-empty-policy \
  -fplugin-opt=LiquidHaskellBoot:--total-Haskell -c "$client"

# Full policy visibility via the plugin namespace must still work.
full=(-hide-package liquidhaskell -plugin-package liquidhaskell -fplugin=LiquidHaskell -fplugin-opt=LiquidHaskell:--no-annotations -fplugin-opt=LiquidHaskell:--total-Haskell)
expect_error plugin-policy "Liquid Type Mismatch" ghc "${common[@]}" "${full[@]}" -c "$client"
ghc "${common[@]}" "${full[@]}" -c "$repo_root/tests/pos/TotalityThrowIONoPrelude.hs" > "$policy_tmp/io.log" 2>&1

# No totality policy is required when checking explicitly opts out.
ghc "${common[@]}" "${boot[@]}" -fplugin-opt=LiquidHaskellBoot:--no-totality -c "$client" > "$policy_tmp/opt-out.log" 2>&1
echo "Totality policy loading: passed (logs: $policy_tmp)"
