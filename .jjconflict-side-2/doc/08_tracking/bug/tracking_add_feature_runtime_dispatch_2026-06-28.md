# tracking add-feature runtime dispatch blocker

- **Filed-on:** 2026-06-28
- **Filed-by:** Codex
- **Area:** `src/app/tracking/main.spl`, app runtime dispatch
- **Status:** Fixed
- **Severity:** medium

## Summary

`tracking add-feature` originally had a focused owner-path implementation and
source checks, but invoking the full app entrypoint with `simple run
src/app/tracking/main.spl add-feature ...` failed before command dispatch while
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

## Fix

`tracking add-feature` now uses
`std.nogc_sync_mut.database.feature_request_rows.add_feature_request_row`, a
narrow database-owner writer for canonical requested feature rows. It avoids the
full generic SDN loader/query stack while still keeping writes out of ad hoc
manual edits.

Positive evidence:

```text
release/x86_64-unknown-linux-gnu/simple run src/app/tracking/main.spl add-feature \
  --id=FR-LLM-RUNTIME-0001 \
  --group=llm_runtime_vllm_torch_interface \
  --title='Prove live local vLLM serving' \
  --source=doc/08_tracking/feature/llm_runtime_vllm_torch_requests.md
tracking add-feature: FR-LLM-RUNTIME-0001
```

## Impact

The new LLM runtime and retry7 requests are tracked in their Markdown source
files and now have canonical `feature_db.sdn` request rows inserted through the
owner-path command.

## Required Fix

- Done: `tracking add-feature` dispatches successfully.
- Done: `FR-SPIPE-LLM-0006`, `FR-LLM-RUNTIME-0001`,
  `FR-LLM-RUNTIME-0002`, and `FR-LLM-RUNTIME-0003` are present in
  `doc/08_tracking/feature/feature_db.sdn`.
- Remaining broader debt: the full generic SDN loader still needs a separate
  runtime cleanup before it is a reliable app-command dependency.
