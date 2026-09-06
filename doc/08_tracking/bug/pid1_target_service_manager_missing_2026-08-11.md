# Missing target-native PID1 service manager

**Status:** Partially resolved — blocks `simple_os_enhance` AC-4 QEMU acceptance

## Evidence

`src/os/kernel/boot/pid1_launch.spl` now prepares
`/system/service_manager.smf` in the live trap scheduler, gives it an explicit
pledged CSpace, makes it the reaper, and permanently closes ambient spawning.
After the reaper binding it also receives the kernel-owned,
non-transferable `root_mint_authority` binding. That binding is not a
`CapabilityToken`, cannot cross IPC/fork, and is cleared on task exit; it is
the required authority base for a future catalog/manifest-mediated service
spawn syscall rather than a return to ambient `CapabilitySet.full()`.
RV64 boot installs that returned scheduler into the trap runtime before the
seal/handoff, and refuses the legacy inline-HTTP fallback if PID1 is absent or
rejected; it returns to the serial recovery console instead.
`src/os/kernel/loader/managed_workload_launch.spl` provides the typed
kernel-side compiled-policy launch seam it must call.
The FAT image writers can stage a supplied target ELF through
`SIMPLEOS_PID1_BINARY` and `SIMPLEOS_REQUIRE_PID1=1`.

The repository now produces `build/os/rootfs/system/service_manager.smf` via
`scripts/os/simpleos-native-build.shs --entry
src/os/services/init/service_manager_main.spl --output
build/os/rootfs/system/service_manager.smf`, and
`build/os/rootfs-riscv64/system/service_manager.smf` via the corresponding
RV64 build wrapper. The build wrapper merges the
single `simpleos_syscall.o` user-ring-3 ABI bridge into the otherwise separate
Simple runtime archive; it does not merge the general C library. The current
local compiler is explicitly the Rust bootstrap seed, so this is integration
evidence only and must be rebuilt with a provenance-valid self-hosted compiler
before a release image can be accepted. A ring-3 entry source now
exists at `src/os/services/init/service_manager_main.spl`: it invokes syscall
136 with opaque VFS, network, and HTTP catalog IDs only. The live dispatcher
accepts that operation only from the current PID1 root-mint holder;
`root_service_catalog.spl` owns each executable path, child grant set, resource
limits, and syscall filter, then routes creation through the ordinary managed
CSpace path. PID1 polls those exact child PIDs through WNOHANG `WaitPid`,
relaunches an exited child with fresh catalog authority, and quarantines it
after three failures. This is not yet boot evidence: the catalogued target
service payloads are still absent. Both bake paths now reject a selected PID1
unless the exact VFS/network/HTTP catalogue artifacts are supplied and staged.

Normal RV64 boot therefore continues to use its recovery path when the image
is absent; it is not evidence of a complete userspace PID1 service manager.
The RV64 architecture syscall gate now delegates syscall IDs 1 (`Yield`), 61
(`WaitPid`), and 136 (`RootServiceSpawn`) to the shared state-threaded syscall
dispatcher. This removes the previous architecture-local `ENOSYS` rejection;
it does not solve the separate RV64 user-task resume path, service payload, or
named endpoint-capability blockers.

## Required resolution

1. Add target-native static builds for the VFS/network/HTTP catalog payloads,
   stage them at the exact catalog paths, and rebuild PID1 with a
   provenance-valid self-hosted compiler.
2. Replace the temporary trusted catalog with signed VFS-loaded
   `WorkloadManifest` records while retaining opaque, broker-mediated kernel
   authority issuance.
3. Set `SIMPLEOS_PID1_BINARY` and `SIMPLEOS_REQUIRE_PID1=1` in the QEMU image
   build.
4. Capture the QEMU scenario: PID1 starts VFS, network, and HTTP in readiness
   order; network crash revokes grants, restarts with fresh grants, reconnects
   HTTP, then quarantines on a restart storm.
5. Replace WNOHANG polling with authenticated kernel exit notifications and
   add readiness/watchdog signals before calling the runtime production-ready.
6. Resolve `catalog_service_named_capability_syscall_mismatch_2026-08-11.md`
   without introducing wildcard IPC or network authority.

## Resume command

```bash
SIMPLEOS_PID1_BINARY=<target-service-manager-elf> \
SIMPLEOS_REQUIRE_PID1=1 sh scripts/os/make_os_disk.shs
```

Then run the repository's RV64/QEMU service lifecycle system scenario once it
has been added.
