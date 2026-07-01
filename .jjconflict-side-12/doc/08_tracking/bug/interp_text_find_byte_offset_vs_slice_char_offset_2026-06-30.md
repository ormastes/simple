# Bug: `text.find` returns a BYTE offset but `text.slice`/`text.len` use CHAR offsets

**Date:** 2026-06-30
**Severity:** Medium — silent data corruption. Mixing `find` with `slice`/`len`
(the natural "find a marker then slice from it" idiom) corrupts substring
extraction whenever the text before the marker contains any multibyte UTF-8
(e.g. an em-dash `—`, 3 bytes). ASCII-only inputs are unaffected, so it hides
until a non-ASCII char appears upstream.
**Component:** Rust seed interpreter — text intrinsics (`find` vs `slice`/`len`
unit mismatch).

## Reproducer

```simple
val s = "ab—cdMARKERxyz"     # em-dash is 3 bytes, 1 char
val i = s.find("MARKER")     # => 7  (BYTE offset)
print(s.slice(i, s.len()))   # => "RKERxyz"  (slice treats 7 as a CHAR offset)
# expected "MARKERxyz"
```

## Impact observed

The torch readiness specs
(`torch/dyn_sffi_ops_readiness_spec`, `torch/torch_training_seed_status_spec`,
`torch/torch_device_placement_status_spec`) read a library `.spl` file and
extract a function body via `find(marker)` + `slice(start, …)`. Library comments
contain em-dashes before the markers, so the body came back missing its leading
chars (`ensor_cuda…` instead of `fn tensor_cuda…`), failing `to_contain` checks.

## Workaround (LANDED)

Those specs now use a char-based `char_find` helper (scans with `slice` so the
returned offset is in the same char units as `slice`/`len`). No assertions
weakened.

## Proper fix (not done)

Make the text intrinsics consistent: either `find` should return a CHAR offset
(matching `slice`/`len`/`substring`), or provide a clearly-named byte/char pair.
Audit other `find`+`slice` call sites for the same latent skew.
