# Native codegen: a parameter named like a top-level `fn` resolves to the fn

**Date:** 2026-10-24 · **Found by:** `.spab` reader spec work (packed_blob_view_spab_spec.spl) · **Status:** open
**Lane:** stage2 `native-build`, x86_64-pc-windows-gnu (prebuilt stage2, 62,730,240 bytes)

## Symptom
Inside a function whose parameter has the same name as a top-level function,
uses of the parameter bind to the top-level function value instead. Here,
`hex_bytes(b, body_sha)` inside `build_blob(body_sha: text, ...)` pushed 7
garbage bytes instead of 32: the callee received the function, not the text.
Renaming the parameter (`digest_hex`) fixed it with no other change.

## Minimal repro
```simple
fn body_sha(x: [u8]) -> text:
    "fn"

fn use_param(body_sha: text) -> i64:
    body_sha.len()          # expected 64 for a 64-char argument

fn main() -> i64:
    print "len={use_param(\"0123456789012345678901234567890123456789012345678901234567890123\")}"
    0
```
Expected `len=64`. Observed in the original case: the parameter read as the fn
value (wrong length / garbage bytes).

## Expected
Lexical scoping: a parameter (or local) shadows any module-level name.

## Workaround
Rename the parameter. Do not convert this into a lint rule; fix name resolution.
