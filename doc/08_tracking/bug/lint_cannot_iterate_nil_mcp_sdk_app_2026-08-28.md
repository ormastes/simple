# `bin/simple lint` dies with `semantic: cannot iterate over this type: Nil` on `mcp_sdk/server/app.spl`

**Date:** 2026-08-28 · **Status:** OPEN (pre-existing, not caused by the 2026-08-28 MCP fixes) · **Severity:** tooling

## Symptom

```
$ bin/simple lint src/lib/nogc_sync_mut/mcp_sdk/server/app.spl
[gc-warning] Higher-layer module 'std.nogc_sync_mut.path' (family: nogc_sync_mut) imported in restricted context (family: nogc_async_mut) (higher_layer_runtime_family)
error: semantic: cannot iterate over this type: Nil
```

No verdict line is printed; the process exits after the semantic error, so
the file cannot be linted at all.

## Pre-existing proof

Reproduced byte-identically on the PRISTINE file at release tip
`359f4419961` (a `git archive` checkout with zero local edits) with the same
binary (goal-bootstrap seed, 60,548,096 B, 2026-08-28 02:53). The
2026-08-28 whitespace-tolerant `app_extract_str` change therefore did not
introduce it.

## Notes for triage

- The error text matches the interpreter's for-in arm miss
  (`src/compiler_rust/compiler/src/interpreter_helpers/collections.rs:563`)
  — the linter itself iterates a `Nil` somewhere while analyzing this file,
  i.e. a linter defect, not a defect in `app.spl`.
- Same error family as the `StrBytes` iteration crash fixed around it
  (`doc/08_tracking/bug/mcp_ctx_batch_execute_crash_hang_on_real_output_2026-08-28.md`):
  `values_for_iteration` fails closed on non-collection values; callers that
  can legitimately hold `Nil`/`StrBytes` need arms or guards.
