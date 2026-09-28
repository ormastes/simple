<!-- codex-architecture -->
# SOSIX positioned filesystem authority plane (draft)

Status: proposed architecture, 2026-09-28. This is an implementation handoff, not runtime or release evidence. It follows the production installation audit in `doc/09_report/simpleos_sosix_positioned_install_blocker_2026-09-28.md` and selected filesystem toolchain requirements REQ-006/007. The F1/F2 positioned-write policy remains for the user to select.

## Observed owners and the missing edge

| Owner | Current authority | Missing edge |
| --- | --- | --- |
| `os.kernel.abi.syscall_shim_positioned` | Retains the backend route and positioned registry state; trap gets the scheduler's caller ID. | No production caller installs a registry owner or publishes capability/buffer transitions into that same state. |
| `os.services.vfs.vfs_boot_state` and `vfs_positioned_ops` | Kernel-global MountTable owns NVFS/DBFS virtual file handles with slot/generation and exact backing mount. | No authenticated client registration maps a live virtual handle to a SOSIX capability. |
| `os.services.vfs.vfs_service` | Catalogue task owns a separate FAT32 `VfsManager` and named `vfs` IPC port. | Its handles and endpoint must not be treated as the kernel-global MountTable's identities. |
| `os.kernel.ipc.ipc` | Owns port IDs, task ownership, copied messages, and authenticated sender facts. | No positioned registration control messages or syscalls consume those facts. |
| `os.sosix.fs.registry_lifecycle_v1` and `service_buffer_registry_v1` | Validate owner, generation, rights, and owned-copy bytes, returning new values. | Values currently remain in tests or local callers and do not reach the retained shim state. |

The current backend route only chooses FAT32/NVFS/DBFS. It cannot authorize an open file, a caller, or a buffer. A numeric endpoint supplied by boot code without a live endpoint owner would create false readiness.

## Composition boundary

Use one portable SOSIX positioned contract with two distinct providers. The kernel-global MountTable provider is the first release target for NVFS/DBFS syscalls 134/135. The catalogue FAT32 task keeps its own copied-IPC provider and must publish its own endpoint/generation if it later joins this contract. No bridge may reinterpret a catalogue `VfsManager` handle as a MountTable file object.

The kernel shim remains the sole mutable owner of its installed registry and backend route. Registration operations must run in that owner or return a transition for it to publish before acknowledging the caller. The caller sends an encoded request or a scoped userspace buffer loan; the kernel copies bytes before retaining them. No user pointer is stored in a registry entry. Trap entry supplies the authenticated task ID; request fields cannot override it.

## Required lifecycle

1. `shim_init` establishes uninstalled state before any mount route. A successful root mount publishes a backend route and a kernel-owned service identity tied to the exact MountTable publication. The service generation and operation generation advance on replacement; exhaustion fails closed. Installation occurs only after both identities and the committed root are live.
2. A new authenticated open/registration control path resolves and authorizes one copied path, opens through `g_vfs_positioned_open`, and binds the returned live MountTable virtual handle to a SOSIX capability with rights and caller ID. If registration fails, it closes that exact virtual handle. The response returns only the capability reference, never a raw driver handle.
3. A bounded owned-copy buffer registration path copies caller bytes, validates access and length, obtains a registry receipt, publishes the returned registry into the installed shim state, and only then acknowledges. Refresh and retirement use the same authenticated sender and endpoint facts.
4. Syscalls 134/135 consume capability and buffer references from that retained state. The existing positioned dispatch owner advances the operation token and publishes registry changes on successful completion.
5. Close retires the capability and its live MountTable object exactly once. Service restart, mount replacement, or shim reinitialization stops new dispatch, retires outstanding registrations, and advances identities before admitting new work. Failed or interrupted registration leaves no acknowledged reference.

The control operation names and numeric syscall/IPC IDs require a registry review before publication. This draft does not assign IDs or claim that the current catalogue service supplies the kernel-global route.

## Route transaction defect to resolve with installation

`boot_nvfs_root_mount_transaction_v1` installs the positioned backend route before `vfs_nvfs_root_mount_commit_v1`. If commit fails, the staged root is aborted or quarantined, but the route remains selected. The DBFS transaction and both boot fallbacks need the same audit. Route publication needs a retained transaction result that either commits with the exact root or can be quarantined on every failed commit without rewinding a generation or invalidating an unrelated newer route. A route-generation comparison alone is insufficient to prove the filesystem root is live.

## Evidence gates

- A real boot installs a root, a live owner, and a registry; no positioned dispatch succeeds before all three publications.
- Two tasks receive distinct capabilities for the same virtual file and cannot borrow one another's references or buffers.
- A successful owned-copy read returns bytes through the registered buffer; a write follows the selected F1/F2 policy. Raw pointers and catalogue handles are rejected.
- Close, failed registration, route-commit failure, and service restart reject stale references without leaving a usable backing object or route.
- QEMU records the actual mount, authenticated control exchange, syscalls 134/135, and terminal retirement. Pure value tests alone do not satisfy release.

Implementation lanes: kernel-global mount/route lifecycle; authenticated registration transport; shim registry publication; end-to-end QEMU evidence. Lower-model sidecars: N/A until the control interface names and fail-fast `step("...")` helpers are fixed in detail design. Merge owner and final reviewer: highest-capability SimpleOS integration owner. No default or release promotion follows this draft.
