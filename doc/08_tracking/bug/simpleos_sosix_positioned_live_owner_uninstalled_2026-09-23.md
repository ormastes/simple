# SimpleOS SOSIX positioned live owner remains uninstalled

Status: source-unfixed; boot route evidence corrected 2026-09-23.

The C-ABI syscall shim retains `g_shim_positioned_state`, reset to uninstalled
by `shim_init`. `shim_positioned_install_owner_v1` has no production caller.
The boot `sosix_positioned_acceptance_round_trip_v1` instead creates a separate
local owner with fixed test identities; its successful NVFS/DBFS/FAT32 backend
transaction does not make syscalls 134/135 usable from a live process.

The VFS IPC service creates a real named port, but no production path binds
that authenticated endpoint/generation to the positioned shim. Likewise,
capability and owned-buffer registration functions are not reached from a
production syscall/IPC lifecycle. Installing an empty or hardcoded boot owner
would only turn `-95` into later `-13` and would falsely imply readiness.

TODO: Add a kernel-authenticated registration lifecycle for service endpoint,
file capability, and owned buffer; install its returned owner after the VFS
service is live; retire entries on close/unmount/process exit; then exercise
both C-ABI positioned traps with real caller identity and bytes in QEMU.
Preserve bounded registry state and O(1) shim dispatch outside the existing
bounded capability/buffer lookup. Do not mark the local route test as live trap
verification.
