# DBFS Root Mount Seal V1

## Scope

This prerequisite lets the canonical `MountTable` attest that `/` uniquely
resolves to a live, device-backed DBFS instance whose transaction owner can
serialize durable namespace replacement. It does not create a server-data
namespace, redeem a launch grant, or wire a syscall.

## Ownership and boundary

`MountTable` owns a bounded array of 64 mutable seal bindings. A caller receives
only `DbfsRootMountSealV1`, an opaque generational lease containing a slot handle
and a DBFS-owner-issued nonce. Revalidation returns immutable copied facts:
mount ID, mount/namespace/content generations, DBFS instance identity, DBFS
owner mutation epoch, and owner nonce. No caller-provided backend name, readiness boolean, path, or generation
is accepted.

The DBFS transaction owner issues the process-lifetime nonce under its existing
checked transaction boundary. This prevents a lease from an abandoned
`MountTable` instance aliasing slot 0/generation 1 after a table reset. Nonce
exhaustion, owner exclusion failure, hosted DBFS, and unavailable durability all
fail closed.

Admission checks exact device registration and mints the nonce in one owner-lock
transaction, removing any unregister race. Every DBFS owner content, namespace,
rollback, or recovery mutation conservatively advances the per-instance epoch;
therefore a retained value copy of the driver cannot mutate around MountTable
generation tracking.

## Lifecycle

Acquisition requires the exact canonical root mount and a `DbFsDriver` whose
device serialization owner is ready. Revalidation compares the active binding,
opaque generation, nonce, exact mount ID, all three mount generations, current
root resolution, and current DBFS instance/readiness. Namespace or content
mutation, unmount, replacement, owner loss, reset, stale reuse, and forged nonce
therefore reject.

Close retires a valid binding exactly once. A stale binding is still retired so
bounded capacity is recovered, but close reports `StaleHandle`; it never turns
stale authority into success. Active seals intentionally do not pin mounts.

## Complexity and storage

Root lookup is O(number of mounts), matching canonical MountTable resolution.
Seal allocation is O(64) worst case with no unbounded growth. Revalidation and
close use O(1) slot lookup plus root resolution. Bindings store scalar identity
and generation facts only; no driver, path, file data, or namespace authority is
copied.

## Acceptance coverage

`test/01_unit/lib/fs_driver/dbfs_root_mount_seal_spec.spl` covers backend and
volatile-root rejection, successful identity/generation sealing, one-shot close,
generation staleness, reset ABA resistance, and unmount invalidation. Execution
is deliberately deferred by the parent task's no-verification instruction.
