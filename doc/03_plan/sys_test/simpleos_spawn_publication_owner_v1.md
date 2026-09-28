# SimpleOS spawn publication prerequisite test plan

Date: 2026-09-14. Status: source-review candidate; runtime **MissingEvidence**.

| Requirement | Executable evidence | Present scope |
|---|---|---|
| REQ-SPAWN-PREP-001 exact frame/SP binding | `test/01_unit/os/kernel/loader/initial_stack_binding_v1_spec.spl` | Four host-fixture scenarios: real checked frame, full extent, alignment/displacement, zero/overflow/out-of-range. Authored mirror under `doc/06_spec/01_unit/os/kernel/loader/`. Execution pending. |
| REQ-SPAWN-PREP-002 explicit child preparation | `test/01_unit/os/kernel/scheduler/scheduler_physical_root_gate_spec.spl` | Source-contract only: common bytes delegation, stack before physical allocation, exact map/entry validation before paired identity reservation, no slot-zero overwrite, packet ENOSYS unchanged. Authored mirror under `doc/06_spec/01_unit/os/kernel/scheduler/`. |
| Existing process image errors and ownership | `test/01_unit/os/kernel/loader/process_image_spec.spl` | Real builder calls assert ABI/embedded-NUL rejection and retained image independence. Existing malformed x86-32 success expectation corrected to existing unsupported-ABI behavior. Historical generated mirror is explicitly stale. |
| Actual physical child publication, wait and rollback | Future canonical owner + candidate-bound CPL0/live-guest scenarios | **MissingEvidence**: no authority may be inferred from the previous three rows. |

Run each focused SSpec once with an admitted native-capable pure-Simple runner,
then docgen the affected manuals and require 0 stubs. The runner is absent now;
do not use a seed or a source-only pass to qualify execution. Lower-level host
model evidence must label the model and does not prove physical mapping.

After physical owners exist, fault-inject every resource reservation and map
operation; race cancellation/exit with commit; exhaust both ready queues; verify
that a child cannot run before VM/caps/TCB publication; observe argc/argv/envp,
priority, attenuated caps and exact assigned PID in the child; collect its exit
once with parent/lifecycle isolation; retain unknown cleanup without slot reuse.
Cold-boot NVFS persistence and compiler-in-guest remain independent gates.

Correction budget: at most three review/fix cycles for this candidate. Retain the
MappingReadLease candidate's previous NO-GO; no reset or replacement model is
permitted to count as that scope's verification.
