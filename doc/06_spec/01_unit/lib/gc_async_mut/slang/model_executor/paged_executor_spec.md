# Slang Physical Paged Executor Lifecycle Specification

> Fail-closed behavior before a compatible physical provider is activated.

| Tests | Active | Skipped | Pending |
|------:|-------:|--------:|--------:|
| 1 | 1 | 0 | 0 |

**Requirements:** `doc/02_requirements/feature/slang_paged_kv_backend.md`  
**Plan:** `doc/03_plan/agent_tasks/slang_paged_kv_backend.md`  
**Design:** `doc/05_design/ml/slang_paged_kv_backend.md`  
**Research:** `doc/01_research/local/slang_paged_kv_backend.md`

## Scenario

Before activation, `paged_executor_active()` is false and generation returns
`PagedExecutorError.ProviderUnavailable`. Shutting down an already inactive
owner succeeds and leaves no state to reclaim.

Executable source:
`test/01_unit/lib/gc_async_mut/slang/model_executor/paged_executor_spec.spl`.

Provider-backed generation is qualified separately by the real-provider smoke;
this unit scenario makes no output-parity or cache-performance claim.
