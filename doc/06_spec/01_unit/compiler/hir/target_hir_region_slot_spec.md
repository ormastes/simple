# TargetHIR region slot protocol

Executable specification: `test/01_unit/compiler/hir/target_hir_region_slot_spec.spl`.

This manual describes authored scenarios. Runtime execution and manual generation
were not performed for the 2026-11-14 generation repair, at the user's request.
These scenarios model sequential lifecycle interleavings; they do not establish
thread-safe publication, compiler bootstrap, or deep HIR immutability.

| Contract | Scenario and expected behavior |
|---|---|
| Slot identity | Snapshot, target and region distinguish keys. |
| THIR-09 | 3,000 same-key claims produce one owner and 2,999 awaiters; all current-generation readers receive the published result. |
| THIR-10 ownership | Non-owner, duplicate and stale-owner publication are rejected; cancellation permits a new generation. |
| THIR-10 completed retry | Cancel generation 1, claim generation 2 and publish its result. Generation 1's waiter receives `region_slot_stale_generation`; generation 2 receives its result. |
| THIR-10 failed retry | Cancel generation 1, claim generation 2 and fail it. Generation 1's waiter receives `region_slot_stale_generation`; generation 2 receives its own failure. |
| Empty slot | Missing slots retain `region_slot_empty` for both zero and nonzero requested generations. |
| IHIR-03 | Two pins share one decoded module in the table. |
| IHIR-06 | The decoded module remains pinned until its last holder unpins. |
