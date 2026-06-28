# tracking add-feature runtime dispatch blocker

- **Filed-on:** 2026-06-28
- **Filed-by:** Codex
- **Area:** `src/app/tracking/main.spl`, app runtime dispatch
- **Status:** Open
- **Severity:** medium

## Summary

`tracking add-feature` now has a focused owner-path implementation and source
checks, but invoking the full app entrypoint with `simple run
src/app/tracking/main.spl add-feature ...` fails before command dispatch while
loading the broader app/compiler closure.

Observed blocker:

```text
error: semantic: method `split` not found on type `array` (receiver value: [])
```

The focused check still passes:

```text
release/x86_64-unknown-linux-gnu/simple check \
  src/lib/nogc_sync_mut/database/feature.spl \
  src/lib/nogc_sync_mut/database/__init__.spl \
  src/lib/nogc_async_mut/database/feature.spl \
  src/lib/nogc_async_mut/database/__init__.spl \
  src/app/tracking/main.spl \
  test/01_unit/lib/database/database_feature_spec.spl \
  test/01_unit/app/tracking/tracking_add_feature_spec.spl
```

## Impact

The new LLM runtime and retry7 requests remain tracked in their Markdown source
files, but their canonical `feature_db.sdn` rows were not inserted because the
repo forbids direct DB edits and the owner-path CLI cannot currently dispatch.

## Required Fix

- Isolate whether the `split` receiver is from CLI arg parsing, app import
  closure loading, or a pre-existing compiler/runtime inference issue.
- Add an executable integration spec for `tracking add-feature` against a
  fixture feature DB.
- Use the owner-path command to insert the pending rows:
  `FR-SPIPE-LLM-0006`, `FR-LLM-RUNTIME-0001`, `FR-LLM-RUNTIME-0002`, and
  `FR-LLM-RUNTIME-0003`.
