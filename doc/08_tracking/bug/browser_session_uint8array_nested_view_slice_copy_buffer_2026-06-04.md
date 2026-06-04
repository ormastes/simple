# BrowserSession Uint8Array nested-view slice copied-buffer gap

Date: 2026-06-04

## Summary

`Uint8Array.prototype.slice.call(view, ...)` is covered for nonzero-offset views,
but a direct `nested.slice(...)` call on a `subarray(...)` of another nonzero
offset view currently behaves as a shared-buffer view in BrowserSession scripts.

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
a copied buffer. The BrowserSession probe failed that expectation, indicating
the direct nested-view `slice(...)` path still aliases the source buffer.

## Impact

Browser scripts that slice a nested typed-array view can observe source-buffer
mutations through what should be a copied result.

## Follow-up

- Route direct `slice(...)` on typed-array view objects through the same copied
  buffer path already used by prototype-dispatched slice coverage.
- Add a regression that proves `nested.slice(...)` returns byte offset `0`,
  has an independent buffer, and remains unchanged after source view mutation.
