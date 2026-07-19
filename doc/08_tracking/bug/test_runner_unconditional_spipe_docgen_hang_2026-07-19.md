# Test runner unconditional SPipe docgen hang

**Status:** SOURCE FIXED / STAGE 4 QUALIFICATION PENDING  
**Severity:** P1 — passing tests could hang before the runner returned

## Root cause

Both sequential and parallel paths unconditionally called
`generate_spipe_docs_for_results`. A passing `*_spec.spl` therefore spawned a
nested `bin/simple spipe-docgen` even for ordinary `simple test` runs. On the
current source runtime that second compiler load emitted a large diagnostic
stream and prevented the outer command from returning.

## Solution

The shared docgen owner now returns unless `options.format == "doc"`, matching
the documented `simple test --doc` contract. Explicit `spipe-docgen` remains
unchanged.

## Reproduction and evidence

- before: MCP stdio spec reached 3 examples, 0 failures, then entered a second
  compiler load and did not return
- after: the same bounded source-runner lane on the bootstrap seed exits 0 in
  39.66s, reports 3 examples, 0 failures and PASS, and performs no post-test
  docgen launch
- the bootstrap essential-tools smoke now rejects both a docgen failure warning
  and an unexpectedly created `doc/06_spec` tree after a default passing spec
- admitted self-hosted Stage 4 evidence: pending
- source launch still emits excessive valid-source recovery diagnostics; that
  independent noise/performance defect remains open
