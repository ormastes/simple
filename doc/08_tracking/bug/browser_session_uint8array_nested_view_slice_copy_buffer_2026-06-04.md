# BrowserSession Uint8Array nested-view slice copied-buffer gap

Date: 2026-06-04

## Status

Fixed in the BrowserSession Uint8Array nested-view slice copied-buffer
continuation on 2026-06-04.

## Summary

`Uint8Array.prototype.slice.call(view, ...)` is covered for nonzero-offset views,
and direct `nested.slice(...)` calls on a `subarray(...)` of another nonzero
offset view now route through the copied-buffer path in BrowserSession scripts.

## Evidence

During the range/string helper continuation, a focused probe used:

```js
var base = new Uint8Array(8);
base[2] = 30;
base[3] = 260;
base[4] = -1;
base[5] = 7;
base[6] = 8;
var view = base.subarray(2, 7);
var nested = view.subarray(1, -1);
var copy = nested.slice(1);
copy.buffer === view.buffer
```

The expected JavaScript behavior is `false`, because `slice(...)` should return
a copied buffer. The BrowserSession probe initially failed that expectation.
The regression now checks the nested source still shares the original view
buffer, the slice result does not share the source buffer, the copied view has
byte offset `0`, and source mutation does not change the copied result.

## Impact

Before the fix, browser scripts that sliced a nested typed-array view could
observe source-buffer mutations through what should have been a copied result.
The direct nested-view slice path now uses copied storage.

## Fix

- Added direct-member typed-array `slice` routing through the copied-buffer
  helper.
- Added `NATIVE_UINT8_ARRAY_SLICE` so `slice` and `subarray` are distinct in
  instance/prototype native method tables.
- Updated the private `__simple_uint8_slice_copy` marker to be a trailing marker
  so `slice()`, `slice(start)`, and `slice(start, end)` all normalize arguments
  correctly.
- Added `copies nested Uint8Array view slice bytes into isolated buffers` to
  `test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`.

## Verification

- Focused BrowserSession check: passed.
- Focused BrowserSession interpreter spec: `234/234` passed with
  `--force-rebuild`.
- Generated manual:
  `doc/06_spec/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.md`
  records `Total scenarios | 234 |`.
