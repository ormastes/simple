# BrowserSession Uint8Array Slice Copy Buffer Gap

Status: open

`Uint8Array.prototype.slice` should return a copied typed array with an
independent `ArrayBuffer`, while `subarray` should keep sharing storage. A
focused BrowserSession probe for copied-buffer `slice` isolation exposed a
runtime dispatch gap: routing `slice` through a separate native helper currently
causes affected BrowserSession scripts to fail with
`semantic: variable 'self' not found`.

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
