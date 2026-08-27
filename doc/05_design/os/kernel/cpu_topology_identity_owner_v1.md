# CPU Topology Identity Owner V1

## Scope

`CpuTopologyIdentityOwnerV1` supplies the immutable hardware-to-logical CPU
identity needed by later quiescence leases. It covers x86 APIC/x2APIC IDs, ARM
MPIDR affinity IDs, and RISC-V boot-assigned hart IDs. It does not wire context
switches, issue leases, track online state, or access architecture registers.

## Ownership and publication

The BSP boot domain owns the sole mutable builder. Entries must be registered
in dense logical-CPU order and the fixed architecture cannot change. Hardware
identities are unique after canonicalization. Capacity is 32, matching the
existing SimpleOS per-CPU ceiling.

Sealing fails for an empty table, permanently closes successful registration,
and returns a read-only snapshot. Boot code must retain that snapshot and
complete its architecture publication barrier before enabling consumers on
other CPUs or in IRQ handlers. This module intentionally does not pretend that
a Simple value copy itself provides that hardware ordering barrier.

## Identity normalization

- x86 stores the full 32-bit APIC/x2APIC identity and rejects wider input.
- ARM retains MPIDR Aff3, Aff2, Aff1, and Aff0, discarding MT/U and reserved
  control bits so aliases cannot describe two logical CPUs.
- RISC-V treats the boot-assigned unsigned hart ID as opaque, including zero.

## IRQ and performance contract

After sealing, lookup methods mutate no state, acquire no lock, allocate no
collection, perform no hardware access, and invoke no runtime boundary.
Logical-to-hardware lookup is O(1). Hardware-to-logical lookup is a bounded
O(n) scan with `n <= 32`; this avoids a duplicate reverse index and keeps the
sealed data compact and cache-local. Registration and duplicate detection are
boot-only O(n).

## Failure policy

Mixed architectures, sparse logical IDs, duplicate canonical hardware IDs,
capacity overflow, invalid wide x86 IDs, and post-seal registrations fail
closed without changing the table. Repeated sealing is observational and
returns the same canonical contents. Empty sealing does not consume the owner,
allowing the BSP identity to be registered afterward.

## Acceptance coverage

`test/01_unit/os/kernel/smp/cpu_topology_identity_owner_v1_spec.spl` covers
bidirectional x86 lookup, dense-order and duplicate rejection, architecture
isolation, MPIDR normalization, post-seal immutability, empty-seal recovery,
and the fixed capacity boundary. Runtime execution is intentionally unverified
for this change.
