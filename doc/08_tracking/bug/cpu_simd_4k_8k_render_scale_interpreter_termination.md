# CPU-SIMD 4K/8K render-scale evidence terminates in interpreter path

## Status

open

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

## Impact

Current evidence can prove CPU-SIMD backend selection, DPI metadata, no
screen-size reduction, checksums, and timing at small dimensions, but full 4K/8K
CPU-SIMD render-loop evidence is blocked until the compiled/native path works
or the interpreter memory/runtime ceiling is removed.

## Required Fix

Fix the native lowering/import path for `web_backend_env_get` in the Simple Web
render backend closure, then rerun:

```sh
sh scripts/check/check-cpu-simd-render-scale-contract.shs
```
