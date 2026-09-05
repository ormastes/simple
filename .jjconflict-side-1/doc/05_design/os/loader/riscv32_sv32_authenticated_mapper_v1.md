# RV32 Sv32 authenticated mapper v1

## Scope

This increment materializes authenticated RV32 ELF `PT_LOAD` pages in a fresh
Sv32 root issued by the architecture owner. It uses the loader registry's
existing joint mapping-pin transaction. It does not publish a task, switch
SATP, perform `sret`, map the initial stack, or make RV32 process-image
readiness true.

## Ownership chain

`riscv32_sv32_mapping_owner_v1.spl` is a serialized four-slot loader capsule.
Each live slot retains the opaque loader transaction, one architecture-issued
root lease, and up to 65,536 PMM-issued `PageFrame` values. No public receipt
contains a destructor or execution authority.

`sv32_user_root_owner_v1.spl` is the serialized architecture capsule. It issues
at most four roots, copies only kernel-half entries 512..1023 from the active
RV32 kernel root, creates lower-half L0 tables, refuses replacement mappings,
and produces the only root-unreachable receipt. Its canonical state is
`NeverActivated`; there is deliberately no SATP/adoption API in this increment.
Detachment requires that state and a zero adoption nonce. A future scheduler
must first add and consume an architecture-owned adoption transition, after
which this never-activated teardown path is unavailable. Public mapping
receipts expose no root physical address. Root and L0 frames remain in
that capsule until the loader registry accepts the exact release coordinate.

## Mapping invariants

- The source length and SHA-256 must equal the authenticated handle, and the
  handle's exact ranges must pass the existing RV32 evidence validator.
- Virtual pages are aligned, nonzero, and below `0x80000000`; physical pages
  are aligned PMM results within Sv32's 34-bit physical range. The same bound
  is checked before encoding every root and L0 page-table allocation.
- Writable mappings are read/write and non-executable. Executable mappings are
  read/execute and non-writable. Replacement PTEs are rejected.
- Each page is zeroed once, then only its authenticated file intersection is
  copied and read back. Work is linear in mapped pages plus file-backed bytes.
- The architecture root identity is bound to the registry before the first PTE
  can become reachable. `Installed` is recorded only after every copy succeeds.

## Rollback and no-UAF ordering

Release first obtains the registry's generation-, nonce-, root-, and
attempt-bound coordinate. Every leaf is exact-unmapped before its retained
`PageFrame` is freed. Failed exact unmaps remain in the bounded slot. Once all
leaves are absent, the architecture capsule validates every owned L0 table is
empty, clears every lower-root pointer, and issues an idempotent unreachable
receipt. The registry accepts only that exact architecture receipt. Only after
registry completion are detached L0/root frames freed.

Indeterminate registry completion retains the detached receipt and returns the
pin to its existing retryable state. Failure after registry completion retains
`RegistryReleased`, so retry can free the architecture resources without
replaying or reopening loader authority. Destroyed slots may be reused only
under a fresh monotonic generation and nonce.

## Remaining readiness boundary

The successful receipt is `MappedBlocked` with
`execution_authorized=false`. RV32 dispatch stays false until a scheduler
capsule atomically adopts the mapping transaction, owns teardown, maps the
four-byte initial stack, publishes the TCB, switches SATP, and performs the
reviewed U-mode transition. Filesystem-backed QEMU evidence remains separate.
