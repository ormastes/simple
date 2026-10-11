# BUG-PHASE1-CACHED-CLASS-ALIAS-IDENTITY-20261011

Status: cached bootstrap producer defect reproduced; no production fix retained.
This is new binder/ownership evidence following
[the capped cleanup investigation](phase1_cleanup_descriptor_visibility_2026-10-11.md).
The earlier three mailbox experiments were not repeated.

## Minimal independent evidence

Current source head: `cf00059acc80e12fe5e44de62dd8536db5d0b6e3`.
Artifact directory: `build/phase1-loader-binder-owner-20261011`.
`class_parameter_probe.spl` contains four ordinary class reference assertions,
with no loader, mailbox, atomic, mapping or dispatch imports.

| Case | Cached producer result |
| --- | --- |
| Direct class function parameter mutation | PASS |
| Class element reached through array parameter | FAIL: text remains empty |
| Class element inside value-struct parameter | FAIL: text remains empty |
| Local class alias taken from an array, with no parameter call | FAIL: text remains empty |

One new cause cycle: 4 executed, 1 passed, 3 failed, exit 1, 1.18 seconds.
Receipts: `binder-cycle1-result.json` and `binder-cycle1.log`.
Probe SHA256: `de5745d5b632ef1cc66ce1da5d6fef34a7abfc56be1435ff4b65586e5ba4e01b`.
No passing case was replayed. Qualification is BOOTSTRAP_ONLY_DIAGNOSTIC.

The local alias failure requires no function-parameter boundary. It therefore
rules out missing loader mailbox state return as the sole explanation. The
cached producer loses class scalar-field updates through aliases; shared
native atomic handles previously concealed that identity failure.

## Bound producer and source owners

Producer SHA256: `15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb`.
`qualification-newseed5f6-hello40/producer-copy.json` records `admitted: false`
and source head `5f6d8b1453be721b9399107bc66ad56f794ebf1e`. The executed binary
also prints its Rust bootstrap seed warning. The metadata associates that
source head with the producer; it is not a production admission manifest.

At the recorded source head, `src/compiler_rust/compiler/src/value.rs`,
`Value::aggregate`, ignores `_is_value_type` and represents both classes and
structs as `Value::Object` with `Arc` field maps. Its existing TODO explicitly
defers reference-class `ClassInstance` identity until field access and method
dispatch support it. `interpreter_call/core/function_exec.rs` simulates direct
argument writeback and merges selected container fields; it cannot preserve
general class aliases when a scalar field forks the object field map.
These are diagnostic source owners, not source changes in this lane.

## Pure interpreter ownership analysis

At the current release source head, both pure `eval_function_call` owners
(`eval_calls.spl` and `_EvalOps/call_method_eval.spl`) distinguish value structs
from classes via `interp_struct_is_value_type`. Class values retain the same
arena ID. `val_struct_deep_copy` retains class field and array IDs when copying
an outer value struct. Local bindings in `eval_stmts.spl` use the same class
preserving gate. `eval_method_with_args` binds self to the existing value ID;
field assignment in `eval_access.spl` writes the global arena's field slot
through `val_struct_set_field_idx`.

That source contract supports class reference identity without an explicit
returned mailbox. It does not prove admitted execution of the pure interpreter,
native class semantics, or the complete loader path. No pure owner defect was
established by this cached producer probe.

Next owner is the bootstrap producer/admission lane for the cached executable's
class identity limitation. Pure interpreter reference checks should be qualified
on an admitted cached runtime separately. No seed source edits, compiler rebuild,
authentication weakening, artificial dispatch, global backlog closure, or
production loader draft changes were made.
