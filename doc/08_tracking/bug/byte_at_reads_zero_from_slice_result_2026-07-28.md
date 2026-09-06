# `byte_at()` reads zeros out of a `slice()` result

**Date:** 2026-07-28
**Status:** Open
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

## Fix

Root-cause the interaction between `slice`'s returned array representation and
`byte_at`'s element read (suspected same family as the nested-array
element-read shred), A/B it against the JIT and native engines, then drop the
copy loop above.
