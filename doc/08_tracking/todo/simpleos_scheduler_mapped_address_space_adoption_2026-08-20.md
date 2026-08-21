# SimpleOS scheduler mapped-address-space adoption

## Status

Implemented, pending admitted-runtime and production-token verification:
`Scheduler.adopt_authenticated_executable_pid_v1` accepts only the loader
registry owner/token coordinates plus ordinary policy inputs. It does not
accept or return an `AddressSpace`, TCB, image capability, or mint seam.

## Canonical owner

`src/os/kernel/scheduler/scheduler_executable_adoption.spl` is the narrow
owner-commit capsule. It consumes the opaque registry token exactly once,
re-reads and validates the retained handle through the shared loader
preparation owner, maps an x86_64 child result, then publishes the TCB, exact
`ProcessVmSpace`, capability record, and ready-queue entry within one canonical
mutable `Scheduler.me` owner transaction. It returns only a PID and receipt. The older
loader-owned map/release compatibility path remains deliberately non-adopting
and reports `legacy-loader-mapped-lease-not-scheduler-adoptable`.

## Required transaction

The scheduler-owned transaction now:

1. validates and consumes the registry-bound loader token without
   exposing `AddressSpace` or a public mint/test seam;
2. reserves one task slot and task ID, builds the architecture-correct user
   context, and registers the exact `ProcessVmSpace` root/id;
3. publishes the TCB and invalidates the loader token exactly once;
4. on pre-publication failure, returns ownership so the scheduler transaction
   destroys the whole x86_64 address space and closes the retained file handle;
5. on post-publication source-close failure, preserve runnable-task ownership
   while quarantining only the retryable close lease; and
6. continues to reject ARM64/RISC-V until a table-tree reclamation owner exists.

The scheduler has no separate general raw mutex; its existing task, ready, and
vmspace mutations are synchronous `me` owner operations. Adoption uses that
same boundary and therefore does not introduce an unrelated lock. Its pure
owner transition is queryable and maps `CommitIndeterminate` directly to
`Quarantined` with authorization false; it cannot trigger duplicate cleanup.

## Rejected shortcuts

- Returning a copyable `AddressSpace` or TCB-bearing capability from a public
  loader API.
- Adding a public scheduler helper that accepts arbitrary roots.
- Treating a receipt, token coordinate, path, digest string, or test-only mint
  as execution authority.
- Enabling ARM64/RISC-V while their current destroy adapters retain boot-life
  roots instead of reclaiming page-table trees.

## Acceptance evidence

- Behavioral tests prove exactly-once adoption, stale/replayed lease rejection,
  full rollback before publication, retryable close after publication, and
  reaping through the scheduler's canonical address-space destroy path.
- Integration evidence uses a token minted by the production cryptographic
  verifier; no public or test-only mint seam is permitted.
- x86_64, ARM64, and RISC-V evidence is reported independently. A supported
  architecture may not stand in for an unreclaimable one.
