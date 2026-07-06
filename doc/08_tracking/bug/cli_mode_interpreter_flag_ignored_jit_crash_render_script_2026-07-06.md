# CLI: `--mode=interpreter` flag ignored, JIT crash on render_simple_html

## Status

Open (two coupled defects).

## Symptom

1. **Flag silently ignored:** `bin/simple run <file> --mode=interpreter` does NOT force interpreter execution — dispatches to JIT path instead. Env var `SIMPLE_EXECUTION_MODE=interpret` works correctly. Gate/tooling honesty: script author believes interpreter is running, but JIT runs.

2. **JIT ARM64 branch overflow crash:** On `tools/pixel_compare/render_simple_html.spl`, JIT crashes with:
   ```
   assertion failed: (diff >> 26 == -1) || (diff >> 26 == 0)
   at src/compiler_rust/vendor/cranelift-jit/src/compiled_blob.rs:90:21
   ```
   Cranelift ARM64 branch-relocation-distance overflow (encoded immediate too small for target distance). Reproduced twice in isolation.

## Evidence

- `scripts/check/check-macos-metal-browser-backing-evidence.shs` invokes `bin/simple run tools/pixel_compare/render_simple_html.spl --mode=interpreter` → Simple lane CRASHES.
- Same script with `SIMPLE_EXECUTION_MODE=interpret` → Simple lane succeeds with bit-exact checksum `329775811848360` matching Chrome/Electron.
- Parity itself is intact (env-var run is correct); this is a tooling/JIT bug, not rendering regression.

## Impact

Tri-lane gate Simple lane crashes as written. Gate credential is misleading (false-red on tooling bug, not actual parity loss).

## Fix direction

1. **Wire the flag:** make `--mode=interpreter` / `--mode=interpret` actually set interpreter mode (resolve same path as `SIMPLE_EXECUTION_MODE=interpret`), OR update gate script to use env var.

2. **JIT robustness:** Cranelift ARM64 far-branch relocation at `compiled_blob.rs:90` is codegen bug for large functions — needs island/veneer insertion or 26-bit branch range handling. Note as JIT-specific limitation; cross-link existing JIT-winit-panic bug if referenced in memory.
