# Workstream D Implementation Notes

## Tests Added

Both new `it` blocks were added to `test/02_integration/app/scv_mvp_spec.spl`.

### Test 1: Same-size byte edits produce different chunk content IDs
- **File:** `test/02_integration/app/scv_mvp_spec.spl`
- **Title:** `"same-size byte edits produce different chunk content IDs"`
- **Closes:** Criterion 2 gap
- **Method:** Writes `hello\n` (6 bytes), snapshots, extracts chunk ID from tree
  object via `awk -F'|' 'NR==1 {print $3}'`. Overwrites with `world\n` (6 bytes,
  same size), snapshots again, extracts second chunk ID. Asserts `id1=sha256_`,
  `id2=sha256_`, and `ids_differ=true`.
- **Pattern reuse:** Uses tree/commit navigation pattern from the existing
  "restore-op fails before writing files when a target chunk is missing" test
  (line 90-98), which already greps `^tree:` from commit objects and reads tree
  rows with `awk -F'|'`.

### Test 2: Binary file restores byte-exactly after snapshot
- **File:** `test/02_integration/app/scv_mvp_spec.spl`
- **Title:** `"binary file restores byte-exactly after snapshot"`
- **Closes:** Criterion 3 gap
- **Method:** Writes binary content via `printf '\000\001\377\376\177\200hello\000world'` (POSIX octal escapes — `/bin/sh` on Linux is usually dash, which does not support `\xNN` hex escapes in `printf`),
  copies original outside repo to `/tmp/scv-binary-orig.$$.bin`, snapshots, captures
  HEAD_OP, overwrites file with `tainted`, runs `restore-op`, then uses `cmp` to
  verify byte-exact match. Binary bytes never pass through Simple text APIs — all
  write/read/compare inside the shell script. Asserts `cmp=match` and `exit=0`.

## Runnability Status

**Blocked by pre-existing compile errors in current source:**

1. `src/lib/scv/public_remote.spl` — `Unexpected token: expected Colon, found LBrace`
   (multi-import `use std.scv.store.{a, b, c}` syntax not supported by `bin/release/simple` Apr 29 binary)
2. `src/lib/scv/delta.spl:16:23` — `reserved keyword 'out' cannot be used as a parameter name`
   (debug/bootstrap compiler)

Both errors are pre-existing and affect **all** scv integration tests, not just
the new ones. The new tests inherit the same blocker.

This is a cross-workstream blocker. WS-D test coverage is complete; runnability
awaits a binary rebuild that supports the new `use {...}` multi-import syntax.

## No Implementation Changes Required

Both gaps were test-coverage gaps only. No changes to `src/` were needed.
