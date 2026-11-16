# Unit TLDR summary surface keeps synthetic names -> "closure identity differs"

- **Status:** verification-pending
- **Date:** 2026-11-16
- **Area:** compiler / 80.driver (streaming surface registration), 20.hir module surface identity
- **Exposed by:** #9608 (`392ff6329c7`), which fixed the earlier "conflicting physical source" stop so builds reached HIR

## Symptom

Phase-2 compiler built from `b45dd8065b5`; every cross lint and test-runner build:

    [hir-shard] owner=1/2@0~h1 inventory publication failed: closure identity differs: published=7b2ad5... worker=755bbb...
    HIR frozen inventory publication failed

The test-runner "exit 1 with no clear error" is the same failure
(`linux-x86_64-test.log:20868`).

## Root cause

`hir_cache_closure_digest` (content rows, default since 2026-11-15) folds each
surface's `rel | content_hash | content_length | module_name | logical_name`.
A HIR shard worker registers each row as a parsed surface, an empty
placeholder or (unit TLDR) a summary surface, depending on its slice.
Parsed and placeholder surfaces take `module_name`/`logical_name` from the
admitted row. Summary surfaces (`module_surface_from_tldr_v1`) keep the names
of their synthetic `<module/id>.spl` path; #9608 rebound only length/hash.
So the digest depended on the worker's slice: in both logs every worker with
`[unit-tldr] summaries=2` failed and the `summaries=0` workers published.

## Fix

`module_surface_bind_row_identity` (module_surface_source_identity.spl) binds
path, index, names and content identity from the row. The streaming TLDR
branch uses it, so a summary surface digests a row the same way as a parsed
or placeholder surface. (The placeholder fast path was reverted upstream in
`7b36dfd615a`; placeholders parse empty text with the row's source identity.) Fail-closed is unchanged. The inventory mismatch text now goes
into the BLOCKED reason, and the MIR aggregate failure line quotes the
ledger's first BLOCKED reason.

Spec: `test/01_unit/compiler/80.driver/unit_tldr_surface_row_identity_spec.spl`.

## Verification pending

The seed specs pass. Driver code is compiled into the binary, so a
redeployed phase-2 compiler and a cross lint/test-runner build are still
needed to verify the fix. No Stage 2 logs for the `compiler_cli_build` and
`test_runner_build` failures were found, only the summary line in
`~/log/matrix_20261116.md`. Their cause is unconfirmed.
