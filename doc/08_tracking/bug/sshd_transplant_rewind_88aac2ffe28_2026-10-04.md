# sshd stale-snapshot rewind via transplant 88aac2ffe28 (2026-10-04)

**Status:** repaired (see PR referenced in the fixing commit).

## What was lost

`88aac2ffe28` ("rebase(main): transplant current main tree onto release/1.0",
single parent `d921e11599e`) replaced `src/os/apps/sshd/` and
`test/01_unit/os/apps/sshd/` with the tree of the pre-rebase main lineage
(`origin/agent/pr1453-required-gate-repair-20260924`, sshd tree `8ac8c0d2`).
That lineage had itself rewound sshd in the share-history merges
`a8244005f9b` / `e274cd33719`: eight of its sshd files were byte-identical to
*older* release blobs, and several more were older blobs plus a few genuine
edits. The true merge base (`b2bd1e635b7`) had sshd == release, so a normal
3-way merge would have accepted every rewind.

Rewound (pure, file == an older release blob): `ssh_cipher`, `ssh_kex`,
`ssh_kex_crypto`, `ssh_kex_primitives`, `ssh_mac`, `ssh_pty`,
`ssh_remote_shell`, `ssh_session_lifecycle`; specs
`ssh_channel_open_capacity`, `ssh_kex_rsa_contract`, `ssh_kexinit_packet_layout`,
and (main edits on a stale base that reverted release fixes, e.g. "empty host
key set advertises nothing" -> "ssh-ed25519") `ssh_kex_hostkey_matrix`.

Rewound in part (older blob + genuine main edits): `ssh_auth` (public-key-only
auth, `ssh_check_public_key_auth` + helpers, `add_user_identity`,
`add_password_verifier`, verifier-only storage), `ssh_channel` (channel-cap /
invalid-id / replay guards, checked window arithmetic), `host_key_loader`
(`file_exists` facade -> raw `rt_file_exists`), `ssh_session_helpers`
(`ssh_session_u8_at`, KEXINIT helpers), plus 8 specs.

## How detected

Session code and specs referenced names with no definition
(`ssh_check_public_key_auth`, `host_key_set_has_any_algorithm`,
`ssh_session_u8_at`, `SshUserDb.add_user_identity`, ...); the x86_64 SSH kernel
(`ssh_ring3_clang_entry.spl`) failed with `hir: cannot infer field type ...
key_blob`. Per-file, the closest historical release blob to the transplanted
file was found; distance 0 identified pure rewinds.

## What was restored

- Pure rewinds: release blob from `88aac2ffe28~1`.
- Partial: release version + only the genuine main additions, reviewed hunk by
  hunk: `SshAuthAttemptBudgetV1` / `MAX_AUTH_EMPTY_POLLS` (ssh_auth),
  `split_whitespace` free-function fix (host_key_loader),
  `_name_list_range_is_well_formed` KEXINIT check (ssh_session_helpers).
  Main-side deletions of release hardening, a dangling
  `export ssh_parse_channel_data_header_v1` (never defined anywhere) and a
  dead `_build_publickey_signed_data` were not taken.
- `ssh_packet_spec`: two error-path vectors predated the release's RFC 4253
  8-byte alignment check (failing at `88aac2ffe28~1` too); re-encoded as
  aligned packets so the intended check is the one that rejects.
- Files main changed on top of the current release blob (`ssh_cipher_live`,
  `ssh_session`, `ssh_session_channel`, `ssh_transport`) and the six files main
  added are kept as-is.

## Crypto (pointed to by the sshd KEX specs)

The same transplant rewound `src/os/crypto/`: 27 of 35 changed files were
byte-identical to older release blobs (`ed25519*`, `curve25519`, `ecdsa_p256/p521`,
`ml_kem*`, `sha384/512`, `aes_gcm*`, `rsa_fallback`, `random`, ...). Those 27 are
restored to `88aac2ffe28~1`; no exported symbol is lost (only private helpers
the release refactor had removed). `curve25519_smalllimb` (patched after the
transplant in `728a98d4791`) gets the transplant diff reverse-applied on top of
that patch, which lands byte-identical to `88aac2ffe28~1` — restoring
`curve25519` alone would have left it calling the removed `_cswap_pair`. Not
touched: `aes128_gcm`, `aes256_gcm`, `paseto`, `pem`, `rsa`, `rsa_pss`,
`sha256` — these mix older content with edits and need a hunk-level review.

## Wider footprint (open)

`88aac2ffe28` changed 44,803 files. Only sshd, its specs and the pure crypto
rewinds are repaired here; the rest of the tree needs the same
closest-older-blob audit (a file byte-identical to an older blob of its own
release history is a rewind, not new work).

## Not restored (pre-existing, different root cause)

Specs that arrived with the transplant reference names that were never defined
on release (also absent at `88aac2ffe28~1`), lost on the main lineage before the
transplant (`4edef8fab8e`, `e274cd33719`) or never landed anywhere — see the
spec table in the fixing PR.

## OS/linker scope audit 2026-10-04

Scope: `src/os/**` (minus `apps/sshd`, `crypto`), `src/os/libc`, `src/os/port`,
`src/lib/{common/contracts,nogc_async_mut}/sosix`, `src/compiler/70.backend/linker`,
`src/compiler/70.backend/backend/simpleos_*.spl`, `scripts/{os,qemu}`.
Compiler-core paths were not touched.

### Method, and why distance 0 was not enough here

For each file `88aac2ffe28` changed in scope: A = `88aac2ffe28~1`, B =
`88aac2ffe28`, history = every blob on release's first-parent history before
`88aac2ffe28~1`. Against the true merge base `b2bd1e635b7`, release had changed
only 2 of the 1003 files (A == base for the rest). So every candidate is a
main-lineage change. 181 of the 207 exact rewinds came from a single main merge,
`83b2e1fecff` ("Merge pull request #94 from ormastes/work/phase3", 2026-08-30).

Rewinds run in both directions. The shared pre-fork history already holds
whole-tree snapshot commits (`4edef8fab8e` "snapshot current development
state", `0a749ba7f10` / `0ac9921e44c` / `b060ff7c996` / `e8444b6b1a6` /
`35c4b52ead6` hourly syncs, `f119f8b7120`, `1c30a048a35`). In some files those
snapshots replaced the newer B with an older A, and main later brought B back.
In those files B is the good version. Example: release's own
`clang_filesystem_signed_catalog_boot_v1.spl` already used the
`SPAWN_RECIPE_CLANG_*` names that only B's `spawn_recipes.spl` defines. An exact
rewind was restored only when all of the following held:
(1) the release commit that moved the file off B is a focused commit, not a
snapshot or sync;
(2) A is not itself an older blob than B (no A -> B -> A);
(3) no file in the current tree imports a name that only B defines;
(4) no seed spec that imports the file newly fails.

### Counts

| class | files |
|---|---|
| scanned (A 377 / D 6 / M 620) | 1003 |
| exact rewind, M (B == older release blob) | 189 |
| - restored to `88aac2ffe28~1` | 116 |
| - kept as is (ambiguous, see list) | 73 |
| exact, re-added by transplant (A == older blob) | 18 |
| - re-deleted: `os/port/llvm/patches/apply.shs` (deleted on purpose in `94fe3f45395`) | 1 |
| - genuine: 13 files that release lost in snapshot `4edef8fab8e` | 13 |
| - candidates, not changed: `os/services/fat32/{fat32,fat32_filesystem_ops,fat32_write,fat32_write_helpers}` (retired in `269830c0288`; `fat32_spec.spl` came back with them) | 4 |
| deleted by transplant: genuine main deletions (`9d0d265fc34` mold linker, `7df0aaba8c2` sosix `io.spl`) | 6 |
| added, genuine | 359 |
| non-exact M | 431 |
| - closer to an older blob than to A (mixed) | 133 |
| - mixed, repaired (release + main's own edits; 8 of them resolve to A) | 23 |
| - mixed, not changed (conflict, ambiguous, snapshot-origin or regressed a spec) | 110 |
| - genuine main edits on the release blob | 298 |

**Repaired mixed files.** Each is a 3-way merge with base = the closest older
blob, ours = A, theirs = B. Every hunk was then reviewed by hand. Hunks that only
reverted release work were dropped: the `context_io` certificate-verification
fields, the `aes128_gcm` collision-safe names, the `riscv_services` network-only
init, the `disk_image_bake` font bundle, and the `xhci_regs` `rt_base`. Genuine
main additions were kept: `errno.h` socket codes, `simpleos_ipc.c` `pipe2`
rollback, `simpleos_libc.c` `<errno.h>` and the `mprotect` note,
`sosix/process.spl` `user_execve`, `arm_fs_exec_dirent` cases, `qemu_runner`
exports and `fpga_boot` gp setup. Main's deletion of `vfprintf`, which has no
other definition, was not taken. The duplicate `EAFNOSUPPORT` and `EOPNOTSUPP`
defines were removed.

**Preserved later release work.** For the arm32 and arm64 timers (#2462), the
`sosix_time_scale_u64` edits were re-applied on top of A. Kept unchanged:
#2458 `mold.spl`, #2452 `stat.h` / `syscall_file.spl` and the `errno.h`
`ENOTSUP` lines, #2384 `mkfs_nvfs.spl`, and the JH7110 drivers. `timer_math.spl`
was not brought back.

**Reverted after spec evidence.** The whole `tls13/` restore set was reverted,
because A's `_Tls13/handshake.spl` does not parse under the seed
(`expected RBrace, found Identifier raw_server_key`). Also reverted:
`simple_web_qemu_panel`, `hosted_browser_renderer_policy`, `vfs_handle_table`,
`percpu` (`rt_simpleos_percpu_online_reset` unknown), riscv64 `hal_smp`,
`memory_leveling_manager`, `sosix/fs/{service_adapter,registered_buffer_client,service_buffer_registry,ipc_codec,service_vfs_backend}_v1`.
In each case main-genuine specs expect main's behaviour, so main has built on B.

### Seed spec evidence

The specs checked are the 175 specs under `test/01_unit/os`, `.../contracts/sosix`
and `.../backend/linker` that `use` a modified module. Each was run with
`/root/work/host-seed-target/bootstrap/simple test` and the `Results:` line was
compared against `origin/release/1.0` (`12e6a0362cf`). Passing examples went
from 1249 to 1267. No spec loses a passing example.

Specs that gained examples:
- `coreutils/chmod`: 5 -> 7 of 8
- `coreutils/cp`: 0 -> 3 of 4
- `coreutils/rm`: 0 -> 2 of 6
- `logging/marker_attrs_schema_validation`: 0 -> 2 of 4
- `logging/marker_registry_attrs_enforcement_class`: 0 -> 2 of 3
- `logging/marker_wire_format`: 1 -> 2 of 8

Two specs moved from a compile failure (1 example, failing) to running all their
examples with partial passes:
- `dbd/dbd_launch`: 2 of 4 pass
- `win_vfs_driver`: 4 of 9 pass

Already failing before and after this change: `tls13/server_entropy_owner`
(7/12) and `tls13/x25519mlkem768_hrr` (0/5). They exercise A-only APIs, but
`tls13/` stays at main's version because of the `handshake.spl` parse failure
above. `tls13/p256_ecdhe_handshake_secret` times out (900 s) both before and
after.

Two hazards for the next auditor:
- One spec in this set deletes the tracked `scripts/os/make_os_disk.shs` from
  the working tree. Run `git status` after spec sweeps.
- A `timeout`-killed spec run leaves its `simple run` child running.

### Kept as is: exact rewinds that are ambiguous (73)

Each needs a per-file owner decision. The usual reason is that release left B
through a snapshot or sync commit, or that main code imports B-only names.

- `os/`: desktop_qemu_contract.spl
- `os/apps/simple_browser/`: simple_browser.spl
- `os/apps/smux/`: smux_contract.spl
- `os/compositor/`: display_backend.spl, engine2d_wm_frame_executor.spl, simple_web_qemu_panel.spl
- `os/drivers/virtio/`: virtio_net_async.spl
- `os/drivers/virtio/_VirtioNet/`: dma_alloc_result.spl
- `os/hosted/`: hosted_browser_renderer_policy.spl
- `os/kernel/arch/arm64/`: cpu.spl
- `os/kernel/boot/`: limine_boot_aarch64.spl, riscv_noalloc_log.spl
- `os/kernel/fs/`: vfs_handle_table.spl
- `os/kernel/loader/`: executable_load_consumer.spl, fs_exec_resolve.spl, guest_toolchain_execution_authority.spl, riscv64_fs_exec_spawn.spl, spawn_recipes.spl, stack_builder.spl
- `os/kernel/memory/`: memory_owned_pages.spl, memory_swap_block.spl, memory_swap_coordinator.spl
- `os/kernel/smp/`: percpu.spl
- `os/kernel/types/`: device_mem_types.spl
- `os/libc/`: simpleos_crt0.S, simpleos_crt0_aarch64.S, simpleos_process_wait.c, simpleos_pwd_stub.c, simpleos_string_ext.c, simpleos_syscall.S, simpleos_syscall_aarch64.S
- `os/libc/include/`: fcntl.h, locale.h, stdlib.h, time.h
- `os/libc/include/sys/`: mman.h, types.h, wait.h
- `os/port/`: e2e_verify.spl, mkfs_dbfs.spl, mkfs_nvfs.spl
- `os/port/llvm/`: build.shs
- `os/port/llvm/patches/simpleos_toolchain_cpp/`: README.md
- `os/posix/`: dylib_async.spl
- `os/proxy/`: socks5.spl
- `os/sdk/include/`: simpleos.h
- `os/services/pkg/`: pkg_service.spl
- `os/sosix/fs/`: ipc_codec_v1.spl, service_adapter_v1.spl
- `os/tls13/`: handshake13.spl, handshake13_ext_builders.spl, handshake13_hrr.spl, hkdf.spl, key_schedule.spl, mod.spl, record13.spl, server.spl, server_builders.spl, server_handshake.spl, server_types.spl, tls13_connect_hrr_p256.spl, transcript.spl
- `os/tls13/_CertVerify/`: der_parsing.spl, signature_verify.spl
- `os/tls13/_Tls13/`: handshake.spl, psk_connect.spl
- `os/tools/pkg/`: pkg_builder.spl
- `os/tools/simplebox/`: simplebox_artifact_contract.spl, simplebox_main.spl
- `os/userlib/`: log.spl, security.spl, system.spl
- `scripts/os/`: simpleos-sysroot-riscv64.shs

### Kept as is: mixed, needs hunk review (110)

- `os/`: cli.spl, machine_profile.spl, qemu_runner_part2.spl, qemu_systest_contract.spl
- `os/_QemuRunner/`: os_build_run.spl, runner_targets.spl, scenario_catalog.spl, scenario_disks.spl, scenario_exec.spl
- `os/apps/dbd/`: dbd_protocol.spl
- `os/apps/servers_user/`: main.spl
- `os/compositor/`: host_wm_theme_bootstrap.spl, hosted_backend_cocoa.spl, hosted_backend_winit.spl, hosted_input_sdl2.spl, hosted_wm_capture_evidence.spl, simple_gui_window_renderer.spl
- `os/drivers/framebuffer/`: fb_driver.spl
- `os/drivers/virtio/`: virtio_gpu.spl, virtio_gpu_ops.spl, virtio_input_ops.spl
- `os/drivers/virtio/_VirtioNet/`: driver_operations.spl
- `os/installer/`: image_builder.spl
- `os/kernel/abi/`: syscall_shim_net.spl
- `os/kernel/arch/`: arch_context.spl
- `os/kernel/arch/arm32/cosmos/`: cosmos_fsbl.c
- `os/kernel/arch/riscv32/`: boot.spl, paging.spl
- `os/kernel/arch/riscv64/`: display.spl, hal_cache.spl, hal_smp.spl, trap_vector.spl
- `os/kernel/arch/riscv64/boot/`: freestanding_runtime.c
- `os/kernel/arch/x86_32/`: paging.spl
- `os/kernel/arch/x86_64/`: paging.spl
- `os/kernel/boot/`: boot_fs_mount.spl, boot_nvme_production_handoff.spl
- `os/kernel/loader/`: arm64_authenticated_media_fixture.spl, arm64_fs_exec_spawn.spl, artifact_manifest.spl, container_namespace.spl, executable_admission_pipeline.spl, executable_crypto_authority.spl, executable_image_prepare.spl, guest_toolchain_execution_contract.spl, primary_linux_tool_catalog_bundle_v1.spl, process_image.spl, riscv64_authenticated_media_fixture.spl, x86_64_authenticated_media_fixture.spl, x86_64_fs_exec_spawn.spl
- `os/kernel/memory/`: memory_leveling_manager.spl, memory_leveling_runtime.spl, memory_leveling_vmm.spl, pmm.spl, vmm.spl, vmm_address_space.spl, vmm_core.spl, vmm_vma.spl
- `os/kernel/net/`: http_baremetal.spl, rt_net_socket_facade.spl
- `os/kernel/scheduler/`: process_execution_observation.spl, scheduler.spl, scheduler_arm_bootstrap.spl, scheduler_exec.spl, scheduler_task_mgmt.spl, scheduler_types.spl
- `os/kernel/types/`: capability_types.spl, ipc_types.spl
- `os/lib/gpu_bridge/`: host_gpu_ivshmem.spl
- `os/libc/`: simpleos_cxxabi.c, simpleos_dlmalloc.c, simpleos_libc_ext.c, simpleos_math_ext.c, simpleos_pthread.c, simpleos_pthread_cond.c
- `os/libc/include/`: pthread.h, string.h, wchar.h
- `os/libc/include/sys/`: stat.h
- `os/ml/`: gpu_tensor.spl
- `os/port/`: cached_raw_image_block_device.spl, initramfs_pack.spl, simpleos_multiplatform_build.spl
- `os/port/_SimpleosMultiplatformBuild/`: build_target_contracts.spl, platform_target_catalog.spl
- `os/port/init/`: simpleos_smoke_init.spl
- `os/port/llvm/`: build.spl, clang_static.shs
- `os/posix/`: dynlib.spl
- `os/services/`: pm_service.spl
- `os/services/evidence/`: __init__.spl, verifier_owner.spl
- `os/services/pcimgr/`: pcimgr.spl
- `os/services/vfs/`: c_nvme_block_adapter.spl, vfs_service.spl
- `os/services/wm/`: wm_codec.spl
- `os/smf/`: smf_dynlib.spl
- `os/sosix/fs/`: kernel_positioned_dispatch_v1.spl, registered_buffer_client_v1.spl, service_buffer_registry_v1.spl, service_vfs_backend_v1.spl
- `os/sosix/qemu_evidence/`: trusted_importer.spl
- `os/tls13/_Tls13/`: context_io.spl
- `os/toolchain/llvm/`: simpleos_cross_toolchain.cmake
- `os/tools/simplebox/`: simplebox_dispatch.spl
- `os/userlib/`: device.spl, process.spl
- `os/userlib/_Window/`: client_methods.spl
- `scripts/os/`: simpleos-sysroot-aarch64.shs
- `src/compiler/70.backend/linker/`: smf_reader.spl

### Out-of-scope candidates (not changed)

- **Test trees.** `test/01_unit/os`, `test/unit/os`, `.../contracts/sosix` and
  `.../backend/linker`: 259 modified and 23 re-added specs are byte-identical to
  older release blobs. Examples: `coreutils/{mem,mv,ps,reboot,run}_spec`,
  `ssh_client/*`, `compositor/{decorations,layout_manager,wm_core}_spec`,
  `linker/{archive_parser,elf_writer}_spec`. List:
  `git diff --raw 88aac2ffe28~1 88aac2ffe28 -- test/...`, filtered by blob-in-history.
  The same both-directions caveat applies. None of the specs that regressed
  during this audit was itself an exact rewind.
- **Legacy FAT32.** `src/os/services/fat32/{fat32,fat32_filesystem_ops,fat32_write,fat32_write_helpers}.spl`
  and `test/{01_unit,unit}/os/services/fat32/fat32_spec.spl` were re-added after
  their retirement in `269830c0288`. Removing them means removing the specs too.
  `vfs_pure_fat_production_guard_spec` already fences production imports.
- **Compiler core and the rest of `src/lib`.** Not scanned (outside scope, and
  Stage 2 debugging is in progress there). The `83b2e1fecff` merge touched far
  more than the OS tree.
