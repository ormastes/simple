# CPU-SIMD 4K/8K render-scale evidence terminates in interpreter path

## Status

fixed

## Evidence

- `sh scripts/check/check-cpu-simd-render-scale-contract.shs` attempted full
  3840x2160 and 7680x4320 CPU-SIMD render-loop evidence through
  `backend_measurement_software_export.spl`.
- The 4K run produced no SDN output and stderr ended with `Terminated`.
- Tiny contract smoke still passes when dimensions are reduced through the
  wrapper environment knobs, proving the contract/parser path works.
- `bin/simple run src/app/wm_compare/backend_measurement_software_export.spl --mode=native`
  falls back to interpreter with:
  `HIR lowering error: Unknown variable: web_backend_env_get while lowering _chromium_tmp_dir`.
- Fixed by importing `env_get` directly in `web_render_backend.spl` instead of
  aliasing it through `mod_stub`.
- `sh scripts/check/check-cpu-simd-render-scale-contract.shs` now passes in
  native mode with full 3840x2160 and 7680x4320 CPU-SIMD rows.

## Impact

Resolved for the native scale contract. Interpreter-only full-size runs remain
too expensive for this lane; the canonical evidence path is native mode.

## Required Fix

No remaining action for this bug.
