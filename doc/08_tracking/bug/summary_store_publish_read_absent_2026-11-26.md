# summary_store: published summary reads back as absent (2026-11-26)

Status: open

## Symptom

`test/01_unit/compiler/cache/summary_store_byte_paging_spec.spl` test 1
("preserves every UTF-8 byte boundary, continuation, and page digest") fails
with `try: early return`, both on the base code (before the strict UTF-8
page-boundary fix) and after it.

## Repro

1. `SummaryStoreV1.memory()`, then
   `store.publish(summary, sha256_text("paging-ast"), "generated/untrusted;public-only")`
   for a summary at path `pkg/é한😀.spl` (snapshot `sha256_text("paging-unicode")`).
2. Wrap it in `VirtualSourceStoreAdapterV1.new(store, ...)`.
3. `facade.read(paging_auth(), snapshot, uri, 0, 1)` returns `Ok` with
   `present=false`, so the spec's `.value?` returns early.

Observed with seed `C:/dev/wt/bound3x-target/release/simple.exe`.
Tests 2 and 3 of the same spec (same publish helper, other paths) pass.

## Impact

The test's page-loop step, which checks that pages end on UTF-8 scalar
boundaries and join back to the full text, never runs, so that part of the
paging contract has no executed coverage.

## Next

Find the root cause and fix it under TDD, so that test 1 passes.
