# RV32 TCB mapping transfer remains blocked (2026-08-24)

The canonical TCB now has an appended, opaque slot/generation locator, but no
present locator is constructed. A reviewed draft tried to bind the existing
`Riscv32Sv32MappingReceiptV1` to a task while leaving that copyable receipt
valid. Its holder could consequently destroy the Sv32 root and registry pin
behind the TCB. An unlock failure after mutation could also strand a bound slot
without returning a handle. The draft was removed.

The safe follow-up needs an owner-consumed transfer state in the serialized
RV32 mapper, invalidation of the loader receipt, durable handling of unlock
failure, publication only after TCB insertion, and task/lifecycle-bound
terminal and reap operations. Until then, the locator stays absent and grants
no activation or readiness.
