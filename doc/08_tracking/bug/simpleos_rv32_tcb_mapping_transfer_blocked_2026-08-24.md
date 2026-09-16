# RV32 TCB mapping transfer remains blocked (2026-08-24)

The canonical TCB now has an appended, opaque slot/generation locator, but no
present locator is constructed. A reviewed draft tried to bind the existing
`Riscv32Sv32MappingReceiptV1` to a task while leaving that copyable receipt
valid. Its holder could consequently destroy the Sv32 root and registry pin
behind the TCB. An unlock failure after mutation could also strand a bound slot
without returning a handle. The draft was removed.

The serialized mapper now has an owner-consumed, exact root/entry/stack and
task-lifecycle-bound transfer with typed committed/rejected/indeterminate
outcomes. It returns only the opaque TCB locator on a determinate commit and
retains a bounded quarantine coordinate when registry or mapper serialization
is indeterminate. The old mapping receipt no longer matches after either
canonical transfer state, so it cannot destroy the retained root behind a TCB.

The remaining blocker is scheduler integration: TCB insertion and transfer
must be one publication protocol with rollback, and task exit/reap must resolve
the locator under the exact task lifecycle before teardown. SATP activation is
also separately owned. Until those are implemented, canonical RV32 dispatch
must keep the locator absent and process-image readiness false.
