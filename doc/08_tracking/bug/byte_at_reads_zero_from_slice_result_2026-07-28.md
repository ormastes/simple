# `byte_at()` reads zeros out of a `slice()` result

**Date:** 2026-07-28
**Status:** Fixed 2026-08-01
**Severity:** High — silent wrong data, no error
**Area:** `std.tls.utilities.{byte_at, slice}`, interpreter (test-runner engine)

## Symptom

An `[i64]` produced by `slice(arr, lo, hi)` has the right `len()`, but every
`byte_at(sliced, i)` reads `0`. Direct indexing of the same array is fine, and
`byte_at` on an array built by a literal or by `.push()` is fine — only the
`slice()` result is poisoned for `byte_at`.

Measured 2026-07-28 while wiring ALPN extraction into the async TLS server
handshake, via
`test/01_unit/lib/nogc_async_mut/io/tls_alpn_negotiation_spec.spl`:

- `parse_alpn_extension([0, 3, 2, 104, 50])` (array literal) -> `"h2"` — PASS
- `parse_alpn_extension(slice(block, 6, 11))` over the same five bytes -> `""`
  — FAIL, even though `len(slice(block, 6, 11)) == 5` asserts green

Inside `parse_alpn_extension` the first read is
`byte_at(ext_data, 0) * 256 + byte_at(ext_data, 1)`; on the sliced array that
evaluates to 0, the `list_len == 0` guard fires, and the function returns `""`.
The length check passing while the reads return zeros is what makes this
expensive to spot — the array looks present and correctly sized.

## Impact

Any `slice()` -> `byte_at()` pipeline decodes as all-zero. In the TLS stack the
pattern appears in `io/tls_handshake.spl` (`extract_encrypted_pms`,
`parse_client_hello_payload` consumers) and wherever a sub-range of a wire
buffer is re-parsed. Failures are silent: zeros are a legal byte value, so
downstream length/type checks just take a wrong branch.

## Workaround in use

Copy the sub-range explicitly instead of slicing when the result will be read
with `byte_at`:

```
var data: [i64] = []
var d = 0
while d < ext_data_len:
    data.push(byte_at(extensions, pos + d))
    d = d + 1
```

`find_alpn_extension_data` in `src/lib/nogc_async_mut/io/tls_handshake.spl`
does this, with a comment pointing here.

## Root cause (2026-08-01)

Not an array-representation bug. Two plain library defects:

1. `src/lib/nogc_sync_mut/tls/_TlsUtilities/text_ops.spl` shipped `append` and
   `len` as **placeholder stubs** — `append(list, item)` returned `list`
   unchanged and `len(collection)` returned `0`. `slice()` builds its result
   with `append`, so it always returned `[]`. (A builtin `len` happened to win
   at the call site, which is why the length assertion looked green while the
   contents were empty.)
2. `byte_at`/`slice` in `_TlsUtilities/hex_encoding.spl` had no parameter or
   return types, so their results were erased to `Any` and read back as `0`
   (or as a raw tag-boxed `value << 3`) at the call boundary.

## Fix

- Implemented `append` and `len` for real; typed `append` as `[i64] -> i64 -> [i64]`.
- Gave `byte_at` and `slice` explicit `[i64]`/`i64` parameter and return types.
- Dropped the byte-by-byte copy loop in `find_alpn_extension_data`
  (`src/lib/nogc_async_mut/io/tls_handshake.spl`); it now calls `slice()`.

Regression: `test/01_unit/lib/nogc_sync_mut/tls/tls_utilities_slice_byte_at_spec.spl`
(7 examples; 5 fail without the fix, 0 fail with it).

Separately found and NOT fixed here: the underlying compiler/seed defect that
zeroes an untyped function's result — see
`doc/08_tracking/bug/untyped_fn_result_erased_to_zero_2026-08-01.md`.
