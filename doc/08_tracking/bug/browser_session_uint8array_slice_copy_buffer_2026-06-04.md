# BrowserSession Uint8Array Slice Copy Buffer Gap

Status: fixed

`Uint8Array.prototype.slice` should return a copied typed array with an
independent `ArrayBuffer`, while `subarray` should keep sharing storage. A
focused BrowserSession probe for copied-buffer `slice` isolation exposed a
runtime dispatch gap: routing copied `slice` behavior through direct evaluator
helper calls caused affected BrowserSession scripts to fail with
`semantic: variable 'self' not found`. The fix keeps `subarray` on the existing
shared-view path and lets `slice` mark the existing range native for a copied
typed-array result through native dispatch.

Observed failing focused scenarios during the probe:

- `slices Uint8Array ranges into returned typed arrays in browser scripts`
- `dispatches Uint8Array prototype range helpers with complementary call and apply`
- `dispatches Uint8Array prototype helpers with call and apply in browser scripts`
- `keeps Uint8Array slice copied buffer writes isolated in browser scripts`
- `encodes browser TextEncoder bytes into WASM validation buffers`

Required fix:

- Preserve existing `subarray` shared-buffer behavior.
- Make `slice` allocate/copy into an independent `ArrayBuffer`.
- Keep direct calls, `Uint8Array.prototype.slice.call`, and
  `Uint8Array.prototype.slice.apply` passing.
- Add a regression scenario proving `slice.buffer !== source.buffer` and
  writes do not cross between the source view and slice result.

Verification:

- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- `SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter` -> `225 passed, 0 failed`
