# Slang Physical-Page Engine Configuration Specification

> Explicit opt-in configuration and resource-bound validation.

| Tests | Active | Skipped | Pending |
|------:|-------:|--------:|--------:|
| 1 | 1 | 0 | 0 |

**Requirements:** `doc/02_requirements/feature/slang_paged_kv_backend.md`  
**Plan:** `doc/03_plan/agent_tasks/slang_paged_kv_backend.md`  
**Design:** `doc/05_design/ml/slang_paged_kv_backend.md`  
**Research:** `doc/01_research/local/slang_paged_kv_backend.md`

## Scenario

Enabled physical paging rejects zero page count, row capacity, prefix capacity,
or byte limit before opening a model or provider. A bounded configuration is
accepted, and explicit disable is accepted before any model is loaded. Engine
unload then succeeds. This unit scenario does not exercise loaded-engine
dispatch between physical paging and the snapshot path.

Executable source:
`test/01_unit/lib/gc_async_mut/slang/engine/physical_pages_config_spec.spl`.

This scenario does not exhaustively cover every provider/profile mismatch;
those clauses remain part of the broader qualification matrix.
