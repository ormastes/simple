# Native HIR: field type not inferred through generic `Result<T,_>` helper; named-const default arg rejected cross-module

Status: verification-pending (source workaround landed; compiler defects remain)

## Symptoms (native-build, release tip 90bfb02453a)
1. `distributed_operation_journal_v2.spl`: `hir: Unsupported feature: cannot infer field type while lowering operation_replay_snapshot_v2: struct 'ANY' field 'database_identity'` (then `authority_digest`, `references` in operation_assessment_held_v3).
   Cause: `val x = generic_helper<T>(...)?` yields `ANY`; field access on it cannot be lowered. Workaround: explicit type annotations on `revision`, `checkpoint`, `manifest`, `entries`, `plan`, `snapshot`.
2. `simple_container_adapter_v2.spl`: `call to 'rejected' omits argument 3 whose default is not a call-site constant`. The default is the named const `RUNTIME_STATUS_BLOCKED`. Workaround: pass it explicitly at 4 call sites.

## Compiler defects still open
- HIR should propagate `T` through generic call + `?`.
- HIR should treat a named module const default as a call-site constant (or resolve it).

## Evidence
Tiny entries importing each module (`std.common.task_runner.distributed_operation_journal_v2.*`, `...simple_container_adapter_v2.*`) failed with the above and now native-build rc=0.
