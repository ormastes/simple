# `std.crypto.sha1` (array-based) lacks `sha1_hex_upper` present in the sibling `std.common.crypto.sha1` (text-based) module

**Date:** 2026-07-20
**Severity:** low (single missing convenience export; text-based sibling has it)
**Status:** fixed — `std.crypto.sha1.sha1_hex_upper(text)` now mirrors the
text-based sibling API while retaining the array-based module's existing
`sha1_hex(text)` conversion path
**Fix owner:** RESOLVED (`codex-par-sha1`)
**Found by:** whole-suite `test/unit/` triage campaign, `lib/common` cluster

## Symptom

```
test/unit/lib/common/crypto/sha1_spec.spl
  ✗ 'abc' uppercase hex
    semantic: function `sha1_hex_upper` not found
```

## Root cause

There are two independent SHA-1 implementations in the tree with diverging
APIs:

- `src/lib/crypto/sha1.spl` — resolves as `std.crypto.sha1` (what the spec
  imports, `use std.crypto.sha1.{sha1, sha1_hex, sha1_hex_upper, ...}` at
  line 25). Functions operate on `[i64]` byte arrays / a `Sha1Context`
  struct. Exports: `sha1_bytes`, `sha1_hex`, `sha1_init`,
  `create_sha1_context`, `sha1_update`, `sha1_finalize`, `sha1_final`,
  `sha1` — **no `sha1_hex_upper`**.
- `src/lib/common/crypto/sha1.spl` — resolves as `std.common.crypto.sha1`.
  Functions operate on `text` / a `(list, list, i64, i64)` tuple context.
  Has `sha1_hex_upper(text) -> text` at line 268
  (`bytes_to_hex(sha1(text)).to_upper()`).

The spec imports from `std.crypto.sha1` (the array-based module), which is
missing the uppercase-hex convenience wrapper that only the
`std.common.crypto.sha1` (text-based) sibling has.

## Resolution

Added `sha1_hex_upper(msg: text) -> text` to `src/lib/crypto/sha1.spl`. It
delegates to the module's existing `sha1_hex(msg)` conversion and digest path,
then uppercases the hexadecimal result. The existing FIPS/RFC `"abc"`
regression passed 11/11; source lint also passed.

## Affected

- `test/01_unit/lib/common/crypto/sha1_spec.spl` — uppercase digest example
  ("'abc' uppercase hex").
