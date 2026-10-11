# Phase 1 actor ABI failures — 2026-10-11

Status: FAIL / draft repair, not admitted.

The original actor contract imported retired std.test, referenced removed
mir_interp_intrinsics.spl and expected retired rt_actor_send_result declarations.
Current legacy generic hooks deliberately reject calls. Correcting those stale
contracts exposed two actual ABI problems rather than completing qualification.

1. The pure MIR runtime owner declared rt_actor_send as returning i64, while
   runtime_sffi.rs registers it with no return values and actors.rs implements
   a void return. This draft switches the declaration and bridge call to the
   existing rt_actor_try_send status API. No provider or allocation changes.
2. LLVM emitter.rs emit_actor_spawn calls rt_actor_spawn with only block_id.
   The runtime registry requires handler and context; block_id is also not a
   proven outlined callback address. The original negative assertion remains
   active and fails. Repair or explicitly reject unsupported spawn in the
   relevant admitted backend before claiming ABI closure. Do not pass a fake
   callback pointer or weaken the assertion.

Retained evidence (workspace build artifacts):
build/phase1-test-imports-20261011/actor-status-abi-repaired.json and .log.
Cycle 2: exit 1, one executed case, zero passes, one failure.
Producer SHA256: 15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb.
Qualification: BOOTSTRAP_SOURCE_CONTRACT_ONLY. The cached producer reads actual
source contracts; it does not prove newly imported production owner execution.

The combined source case reports a final assertion failure, not a count of all
independent ABI defects. Full production and native/MCP admission gates remain
pending. The historical 4,758 queue is not a current failure count.

Independent backend_audit review found no introduced P0/P1: RuntimeValue's
transparent u64 representation matches the existing raw handle boundary, and
the declaration/call change matches the registry and implementation together.
Working and staged direct-env guards passed; tracked doc/06_spec executable
spec count is zero. The source-only SFFI audit passed four inventory assertions
and emitted 10,962 existing debt rows; admission remains absent. This broad
ledger is not qualification of this actor repair or a zero-debt verdict.
