# `std.crypto.sha1` (array-based) lacks `sha1_hex_upper` present in the sibling `std.common.crypto.sha1` (text-based) module

**Date:** 2026-07-20
**Severity:** low (single missing convenience export; text-based sibling has it)
**Status:** open — needs a product decision (add the export, or fix the test's
import path), not a mechanical test-only fix
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

## Fix needed (not attempted — out of test-triage scope)

Either:
1. Add `sha1_hex_upper` to `src/lib/crypto/sha1.spl` — trivial in isolation
   (`bytes_to_hex(sha1(...)).to_upper()`), but that module's `sha1()` takes
   `[i64]` not `text`, so the wrapper also needs a `text -> [i64]` encode
   step matching this module's existing `sha1_hex(text)` convention (see
   line 107 of that file for the pattern to mirror); or
2. Point the spec at `std.common.crypto.sha1` instead, if that is the
   intended canonical module — but that changes every other call in the
   spec too (their signatures are `text`-based vs `[i64]`-based, not just
   this one function), so it's not a 1-line import fix.

Deciding which of the two SHA-1 modules is canonical (or whether both should
exist and stay API-parity'd) is a product/architecture call, not something
to guess at from test-triage scope. Left the spec unmodified.

## Affected

- `test/unit/lib/common/crypto/sha1_spec.spl` — 1 of 11 examples
  ("'abc' uppercase hex").
