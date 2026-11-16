# Managed workload launch specs hardcode an x86_64 image; adoption rejects it on arm64 hosts

- **Status:** closed (2026-11-15, work/container-launch-gaps-20261115)
- **Where:** `src/os/kernel/scheduler/scheduler_executable_adoption.spl:207`
  (`_authenticated_consumer_arch_matches_v1(consumer, get_arch())`), with specs
  `test/01_unit/os/kernel/loader/managed_workload_launch_spec.spl` (3/5),
  `test/01_unit/os/services/container/container_runtime_spec.spl` (4/5),
  `runtime_provider_v1_spec.spl` (2/3), `macos_simpleos_guest_dispatch_v1_spec.spl` (2/3)
- **Host:** macOS arm64, rebuilt seed with the registry fix

## Evidence
On this host, `get_arch()` is `@cfg(arm64)` -> `Architecture.Arm64`. The specs
build `_minimal_x86_64_elf()` and pass `Architecture.X86_64`. Adoption returns
`RollbackUnavailable`. The cleanup release then returns `CloseFailed`, and the
caller sees `pid=-13`. On an x86_64 host the same path would reach publication.

## Unblock
Choose one: (a) the specs build a minimal ELF for `get_arch()`; or (b) the owner
approves an arch tag (only `# @platform:` OS tags exist). Do not skip these specs
without approval. Separately, the cleanup `CloseFailed` after an arch rejection
should be checked; a rejected adoption should release cleanly.

## Update 2026-11-15 (work/container-launch-host-arch-20261115)
Fixed (this change):
- Spec fixtures now build an ELF whose `e_machine` matches `get_arch()`
  (`_minimal_host_elf` / `_host_elf_machine`) and launch with `get_arch()`;
  the guest-dispatch drift case uses `_foreign_arch()`. Assertions unchanged.
- Product: arm64 arch text mismatch. `managed_image_authority_v1.spl` emitted
  `"arm64"` and `scheduler_executable_adoption.spl:140` expected `"arm64"`,
  but the loader contract (`executable_load_plan_v1.spl:146`,
  `artifact_manifest.spl:255`) only accepts `"aarch64"`, so every arm64
  managed issue failed with -8. Both now use `"aarch64"`.
- Product (arch-independent): `managed_image_authority_v1.spl` handed adoption
  an already-`Validated` consumer; `executable_prepare_image_v1` re-plans and
  requires `Ready`, so it always failed `InvalidConsumer`. It now validates a
  plan but returns the Ready consumer. The earlier claim that an x86_64 host
  "would reach publication" was unverified and is withdrawn.

Cleanup bug FIXED (follow-up, same branch):
- Root cause refined: drivers are value structs in `DriverInstance`; a driver
  method that mutates scalar state (RamFS `next_fd`, `fd_table` reassignment)
  on the matched copy was lost. `open_for_execute` / `open_stable_snapshot`
  additionally ran every driver call on a `val entry = self.mounts[i]` copy, so
  the execute fd never reached the mounted driver and `close` returned
  `InvalidArg` -> loader `CloseFailed`.
- Fix: mutating dispatch functions in
  `src/lib/nogc_async_mut/fs_driver/mount_driver_dispatch.spl` now return
  `(DriverInstance, Result)`; `MountTable._wb_*` helpers
  (`mount_table.spl`) store the updated driver back into `mounts[i].driver`.
  All 36 call sites go through them, including the two `entry` copy blocks and
  `close_stable_snapshot`.
- Specs: reproducer + generalization
  `test/01_unit/lib/fs_driver/mount_table_driver_writeback_spec.spl`
  (execute open->close, ordinary open/double-close, mkdir persistence, two
  independent execute handles): 2/4 before -> 4/4 after. Arch/consumer fixes:
  `test/01_unit/os/kernel/loader/managed_image_authority_host_arch_spec.spl`
  3/3. Shared fixture: `test/helpers/host_arch_elf_fixture.spl`.
- After the fix a rejected launch releases cleanly (`release -> Ok(())`).
- fs_driver specs (`test/01_unit/fs_driver/*`, `test/01_unit/lib/fs_driver/*`):
  identical verdicts before/after except the new spec; pre-existing failures
  unchanged (mount_table_test 15/27, mount_table_resolve_test 1/6,
  mount_table_execute_path_open 6/10, stable_file_snapshot 9/11,
  nvfs_pure_simple 7/12, nvfs_streaming_ingest_adapter 0/5 and _source 0/1,
  file_block_device_owner_contract 0/3, fat32_cache and file_block_device
  0 executed).

Still open (next blocker, arm64 hosted only):
- The four launch specs now fail at `AddressSpaceUnavailable`:
  `scheduler_executable_adoption.spl` `_address_space_can_map(space)` after
  `create_user_address_space()`, which on `@cfg(arm64)`
  (`src/os/kernel/memory/user_address_space.spl:46`) calls the kernel extern
  `rt_arm64_user_as_create`, which has no hosted backing. Unblock: a hosted
  arm64 user-address-space provider (like the x86_64 `vmm` path), or run these
  specs on an x86_64 host. Verdicts unchanged at 2/5, 4/5, 2/3, 2/3.

## Update 2026-11-15 (work/arm64-host-user-as-20261115) — still OPEN

Verdicts on this arm64 Mac (seed release100-matcharm-20261115), before -> after:
managed_workload_launch 2/5 -> **5/5**; container_runtime 4/5 -> 4/5;
runtime_provider_v1 2/3 -> 2/3; macos_simpleos_guest_dispatch_v1 2/3 -> 2/3
(the three container specs now get past launch and fail on later gaps below).
New: `test/01_unit/os/kernel/memory/arm64_hosted_user_address_space_spec.spl` 3/3
(its assertions run only when `get_arch() == Arm64`; zero assertions elsewhere).

Findings (corrections to the earlier "Unblock"):
- There was no x86_64 hosted provider to twin: hosted, every non-arm64 arm
  goes through `vmm_address_space.spl:86` and returns `root=1 id=0` (VMM not
  initialized), which `_address_space_can_map` rejects. The arm64 model is new.
- Binding defect: `scheduler_executable_adoption.spl` imported
  `create_user_address_space` from `user_address_space` but the call bound to
  `vmm_address_space`'s same-named pub fn (proved with markers). Worked around
  with an import alias; the same pattern is still live at
  `executable_load_consumer.spl:301`.
- `@cfg(baremetal)` / `@cfg(not(baremetal))` is ungated in the seed
  interpreter (`cfg_strip.rs:28,321` gate arch names only), so both twins load.
- The hosted `*_host_stub` functions never satisfied their externs; renamed to
  the extern names (precedent: `segment_mapper.spl` `rt_arm_elf64_direct_entry`).
- Hosted `[u8]` is not the packed freestanding header, so the
  `not(x86_64)` `vmm_copy_bytes_to_phys` raw memcpy SIGSEGVs; element-wise copy
  under the hosted model.
- Not verified: an arm64 freestanding kernel compile with these changes
  (not run on this host).

Arch-independent product gaps found past the address space (commit 2):
- `managed_workload_launch.spl`: nothing called `bind_managed_child_security`
  (no caller in any ref), so every later binder failed `policy_bound` -> -12.
  Now bound to the caller's TCB resource domain.
- No process-limit admission existed for 64-bit managed launch; added
  `sched_resource_process_admits` (authority_runtime.spl) checked before
  staging -> -11.
- `ContainerWorld.bind_runtime_pid` was called (`container_runtime.spl:102`)
  but never defined; implemented.
- Container specs never initialized the loader authority owner (boot does);
  shared `ensure_loader_authority_registry()` in `test/helpers/host_arch_elf_fixture.spl`.

Still open:
- `task_exit_teardown.spl:7,25` imports/calls `device_grant_revoke_task`, which
  no ref has ever defined. `_handle_device_grant` registers RES_NOTIFICATION /
  RES_IRQ_ROUTE via `task_register_resource`, which `task_cleanup` may already
  reclaim: delete-the-call vs add-a-ledger is an owner decision. Blocks
  container_runtime and macos_simpleos_guest_dispatch_v1 exit tests.
- runtime_provider_v1 "binds a real task..." returns `rejected` (undiagnosed).
- Missing generalization spec: launch from a forked member of a limit-1
  workload must return -11.

## Update 2026-11-15 (work/container-launch-gaps-20261115) — CLOSED

Verdicts on this arm64 Mac (seed release100-matcharm-20261115), before -> after:
container_runtime 4/5 -> **5/5**; runtime_provider_v1 2/3 -> **3/3**;
macos_simpleos_guest_dispatch_v1 2/3 -> **3/3**; managed_workload_launch 5/5 -> **6/6**.

- `device_grant_revoke_task` call deleted from `task_exit_teardown.spl`: a
  device grant's only state is the RES_NOTIFICATION / RES_IRQ_ROUTE entries
  `_handle_device_grant` registers through `task_register_resource`, and
  `task_cleanup` (already called in the same teardown) destroys/unregisters
  both. BAR/IRQ/DMA tokens are pure functions of (bdf, task) with no ledger.
- `Scheduler.live_job_member_ids` / `Scheduler.terminate_job` were called by
  `container_runtime.spl:164` and `agent_runtime.spl:100` but never defined
  (the next blocker once the teardown call was gone). Added
  `sched_live_job_member_ids` / `sched_terminate_job` in `authority_runtime.spl`,
  sharing `_authority_close_job` with `sched_terminate_direct_child_job`.
- runtime_provider_v1 `rejected` root cause: its ELF fixture had
  `p_offset 0x80` with `p_vaddr 0x400000` (align 0x1000), violating
  offset/vaddr congruence, so launch returned -8. Fixture now uses 0x400080,
  like container_runtime's. Spec bug, not product.
- `executable_load_consumer.spl` imports the user-address-space pair under
  `user_as_create` / `user_as_destroy` aliases (same fix as adoption).
- New spec "charges a forked member against its limit-1 workload before
  launching" (`managed_workload_launch_spec.spl`) -> -11. Needed
  `vmm_cow_clone_pages` to be `pub` (imported by scheduler_exec,
  scheduler_task_mgmt, vmm_vma; was private, so fork failed hosted).

Not fixed (seed parser gap, needs a seed rebuild):
`scheduler_security_contract_spec.spl:155` `security.policy_bound = true` fails
`expected identifier, found Dot`. `src/compiler_rust/parser/src/parser_impl/core.rs:901`
treats every statement-leading identifier `security` as a security policy/gate
declaration without checking for a following `.`/`=`. The spec is valid Simple.
Unblock: make that arm contextual (like `admit`/`move`) and rebuild the seed.
