# SimpleOS Architecture Doctrine

**Status:** Draft architecture doctrine.

**Purpose:** This document defines the architectural direction for SimpleOS API
layers, async behavior, compatibility shims, and MDSOC placement. It is the
policy layer above the frozen interface details in
[`simpleos_interfaces.md`](simpleos_interfaces.md) and the source layout rules in
[`simpleos_layout.md`](simpleos_layout.md).

## Core Doctrine

SimpleOS provides POSIX and libc compatibility so existing C, C++, Rust, and
Unix-oriented software can be ported. POSIX is not the native programming model.

Native SimpleOS drivers, kernel subsystems, services, and apps should use the
native SimpleOS API:

- kernel code uses MDSOC ports, HAL contracts, scheduler, memory, IPC,
  capability, VFS, and device-service contracts;
- drivers use driver and HAL interfaces, not POSIX or libc;
- services use native IPC, capability, VFS, process, clock, pipe, TTY, socket,
  and window protocols;
- apps use `src/os/userlib`, `src/os/async`, and service-specific native
  facades;
- POSIX and libc code stays in compatibility/porting layers and should be thin
  wrappers over native services.

The architectural direction is async-first. SimpleOS native I/O, process,
timer, pipe, terminal, socket, device, and window operations should define their
native async behavior first. Synchronous APIs are allowed only as wrappers that
block or wait on the async operation.

## API Tiers

| Tier | Location | Role | Who should use it |
| --- | --- | --- | --- |
| Native SimpleOS API | `src/os/userlib`, `src/os/async`, service protocols | Primary userspace API over syscalls, IPC, capabilities, and notifications. | SimpleOS apps and user services. |
| Kernel/driver API | `src/os/kernel`, `src/os/drivers`, MDSOC ports | Ring-0 and hardware-facing contracts. | Kernel subsystems and drivers only. |
| POSIX/libc compatibility | `src/os/posix`, `src/os/libc`, language PAL ports | Porting veneer over the native API. | Ported C/Rust/POSIX software and compatibility tests. |

The dependency direction is:

1. kernel, drivers, and services provide native async operations;
2. native userlib exposes async-first operations to apps and services;
3. POSIX/libc sync calls block on native async completions;
4. language runtimes and ported libraries consume POSIX/libc only when they
   cannot reasonably target the native API directly.

Native SimpleOS code should not depend on POSIX merely because a synchronous
shape is convenient. Add a native async API, then add sync convenience wrappers
where needed.

## Capability-Backed Storage And Devices

SimpleOS uses an exokernel-style control-plane/data-plane split for storage and
devices. This does not mean normal apps receive raw hardware. It means the
trusted control plane allocates, bounds, accounts, and revokes resources, while
native apps and library OS code receive explicit capabilities for the policy
they are allowed to control.

The detailed storage/device target is recorded in
[`simpleos_exokernel_storage_architecture.md`](simpleos_exokernel_storage_architecture.md).

Native storage and device APIs should expose capabilities such as:

- block device, namespace, partition, mount, and storage extent handles;
- I/O queue handles for trusted async data paths;
- device BAR, IRQ, DMA, and IOMMU handles only for trusted driver capsules.

POSIX paths and file descriptors are compatibility views over these native
handles. Drivers and native services should not use POSIX paths as their
authority primitive.

For NVMe, `QID 0` is the admin queue, `QID 1` is the reserved system I/O queue,
and `QID 2+` is available for policy-managed data queues. App data traffic must
not be allowed to starve the system queue.

## Async-First Requirement

Every new SimpleOS subsystem that performs I/O, waiting, or cross-task
coordination must define an async-native contract before adding synchronous
wrappers.

Required async-first subsystems include:

- VFS and file descriptors;
- stdio, terminal, TTY/PTY, and pipes;
- process spawn, exit, wait, and lifecycle notifications;
- timers, sleep, and timeout APIs;
- sockets and network service APIs;
- window/compositor event and update APIs;
- device service requests and completion notifications.

Synchronous APIs should be implemented by waiting on `OsFuture`, `OsWaker`,
notifications, completion ports, or equivalent native async objects. Busy loops
are transitional only and must be documented with removal criteria.

If an existing subsystem is sync-first, it remains valid only as a transitional
compatibility path. The owning plan must add a TODO that names the native async
contract to introduce and the sync wrapper that will move on top of it.

## POSIX Compatibility Policy

SimpleOS should provide a useful POSIX subset, but POSIX is a compatibility
surface:

- `src/os/posix` maps POSIX-style file descriptors, pipes, sockets, signals,
  process calls, `select`, and `poll` onto native SimpleOS async IPC and
  services;
- `src/os/libc` exposes C ABI and libc symbols for ported software;
- Rust PAL and other language ports may use POSIX/libc when required by their
  upstream runtime model;
- SimpleOS-native apps should prefer native userlib APIs over POSIX wrappers;
- drivers and kernel subsystems must not import POSIX/libc.

The POSIX layer may expose synchronous APIs because POSIX is synchronous by
default. Those implementations must still be layered over native async
operations. For example, `read`, `write`, `poll`, `pipe`, `waitpid`, and stdio
should route through native fd, notification, pipe, TTY, VFS, and process
services rather than bypassing them.

## MDSOC Placement

SimpleOS uses MDSOC for subsystem boundaries:

- `src/os/kernel` and `src/os/drivers` are MDSOC-only. Do not use ECS in ring 0
  or driver state machines.
- `src/os/services` and `src/os/apps` are MDSOC+ where appropriate: the outer
  boundary is MDSOC, and long-lived userland domain state may use ECS
  internally.
- `src/os/userlib` is the native userspace facade and must not become a state
  owner for POSIX compatibility.
- `src/os/posix` and `src/os/libc` are compatibility veneers.
- Shared syscall, IPC, fd, process, pipe, and TTY contracts belong in shared
  type/protocol modules, not duplicated across sibling capsules.

When a native service and a POSIX wrapper need the same contract, the contract
belongs in the native service or shared protocol layer. The POSIX wrapper should
adapt to that contract.

## Current Transitional Gaps

The repo already has pieces of the target architecture:

- `src/os/async` defines an OS async runtime based on futures, wakers,
  notifications, and wait-any behavior.
- `src/os/posix/mod.spl` documents POSIX as sync wrappers over async IPC.
- VFS, pipe, TTY, process, launcher, and libc paths exist but are not yet fully
  unified around kernel-owned process/fd objects and native async completions.

The following paths should be treated as transitional until they route through
native async contracts:

- POSIX fd I/O paths that do not yet share kernel-owned fd and open-file state;
- pipe compatibility code that is not unified with service/kernel pipe objects;
- libc stdio paths that bypass fd routing for stdout/stderr;
- shell builtins that write directly to terminal UI instead of fd-backed output;
- process wait/spawn wrappers that do not carry full argv/env/cwd/stdio/cap
  requests;
- sync file, pipe, timer, and terminal calls that wait through polling rather
  than explicit native completion objects.

These gaps are tracked in
[`simpleos_missing_os_subsystems_report.md`](../03_plan/agent_tasks/simpleos_missing_os_subsystems_report.md).

## Review Rules

Reject new SimpleOS code when it violates these rules:

- a driver imports POSIX/libc;
- kernel code imports POSIX/libc or userlib convenience wrappers;
- a native app or service adds a POSIX dependency where a native userlib/service
  API exists;
- a sync-only subsystem is added without an async-native contract;
- a compatibility shim becomes the state owner instead of adapting to native
  service state;
- protocol or ABI structs are duplicated in sibling modules instead of shared
  through an MDSOC contract.

When an exception is unavoidable, document it as transitional and include the
removal condition in the owning plan.
