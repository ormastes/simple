# Validate indexed source bytes before private-import admission

The basic sparse-checkout correction, PRIVATE_IMPORT_BASE CI handoff and
confirmed-absence/read-error distinction landed before this follow-up. This change preserves that entry contract,
readable-commit guard, complete existing selftest body and working-tree authority.
It strengthens input validation; it does not replace the landed repair with skips.

Only absent stage0 regular SKIP_WORKTREE entries may be copied to a fresh private
prefix with checkout-index, without -u. Raw hash-object --no-filters IDs must
match actual index IDs. Attribute/smudge transformations and indexed symlinks
fail explicitly; present source must resolve inside the root. All intermediate
writes are checked, mappings require complete positive counts, and AWK selects
inputs by FILENAME rather than the empty-first-file-sensitive NR==FNR idiom.
Newlines within NUL-delimited index filenames fail before line conversion, so
they cannot forge another sparse metadata record.

The baseline and removal-only policy remain unchanged. The landed ratchet still requires a valid commit with confirmed baseline-path
absence; its readable-commit and unavailable-blob/read-error guards and tests
are preserved byte-for-byte, not replaced by an older local implementation.

Controls retain the landed cases and add staged/indexed authority, physical
newline parity, raw attribute mismatch, sparse symlink rejection, unchanged
index/worktree, real write failure, empty mapping and actual newline-index
fixtures. The scanner helpers match the already qualified corrected shell candidate;
unchanged whole green suites were not replayed locally on this new composition. Exact-head Astra review
and real CI are still required before landing.

This is shell/awk, Git and realpath tooling, with mode100644 and no Python.
Indexed copies consume temporary disk proportional to selected absent bytes.
Promisor repositories may lazily fetch blobs; no single/network-free-fetch claim
is made. Existing job limits and the unchanged printf/head publisher still apply.
No compiler/MCP source, baseline exemptions or native artifact is changed.
