# Source-grep guard specs un-modernizable until a self-hosted binary is deployed

- Date: 2026-08-26
- Found via: sspec modernization residual wave (batch ba, ~56 specs scoring 49 /
  SSDOC-ORA-002).

## Class

These specs pin `src/app/**` implementation shapes via source-grep assertions
(`expect(source.contains(...))`). Behavioral oracles are unreachable on the
current deployment: `bin/simple` is the **Rust seed** (banner verified), and
this worktree has no `bootstrap/` stage binaries (tracked stage artifacts
absent; per the 2026-08-18 guard record they SEGV anyway). The seed's `lint`
emits findings only as unscoped startup noise over compiler sources — never a
`-->`-scoped diagnostic for an arbitrary fixture — so a scoped behavioral
oracle against the pure-Simple CLI paths cannot be built.

Faking behavioral assertions against the seed would test different code than
the specs pin and violate the never-weaken rule, so they are left as-is.

## Unblock

Deploy a working self-hosted `bin/simple` (`scripts/setup/setup.shs && bin/simple
build bootstrap`), then rewrite each source-grep scenario to invoke the real
CLI (`rt_process_run`) and assert observable output.

## Representative members

- `test/01_unit/app/auto_coverage_*_spec.spl` (12)
- `test/01_unit/app/branch_coverage_*_spec.spl` (~19)
- `test/01_unit/app/test_runner/**` guard specs
- `doc/06_spec/x25519mlkem768_*` mirror owners (7 mirrors misplaced — sources
  live under `test/01_unit/app/test/`, mirrors need relocation after the specs
  are fixed)

## Batch resid6_part_02 (2026-08-27): blocked-classes, one line of evidence each

ORA-002 source-mechanism contracts (assertion is a code-shape property of `src/**` with no host-callable oracle):
- `test/01_unit/os/apps/servers_user/dbd_filesystem_provisioning_spec.spl` — reads `src/os/apps/servers_user/main.spl` provisioning source shape.
- `test/01_unit/os/crypto/x25519mlkem768_absolute_spec.spl` — C guard layout of `src/runtime/runtime_simd_dispatch.c` (MSVC vs GNU attribute placement).
- `test/01_unit/os/crypto/x25519mlkem768_accelerator_cache_spec.spl` — implementation-shape reads of `src/os/crypto/x25519_mlkem768/*`.
- `test/01_unit/os/crypto/x25519mlkem768_native_tagged_value_contract_spec.spl` — asserts `byte_decode` is ABSENT from `src/os/crypto/ml_kem.spl` (negative mechanism oracle; the behavioral half of the spec is already modern).
- `test/01_unit/os/desktop/desktop_e2e_shortcut_flow_spec.spl` — reads DESKTOP_E2E_ENTRY source; e2e desktop flow needs a running desktop session.
- `test/01_unit/os/drivers/framebuffer/bga_scanout_evidence_spec.spl` — `src/os/drivers/framebuffer/bga_init.spl` register-write shape; needs QEMU/board scanout.
- `test/01_unit/os/port/qrb2210_*_spec.spl` (5) — QRB2210 board provider/entry/ports source contracts; physical-board targets.
- `test/01_unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl` + `.spipe_wrapped_entry_` twin — NVMe boot lease source contract.
- `test/01_unit/runtime/argv_provider_source_contract_spec.spl` — `src/runtime/simple_core/core_process.spl` + `simpleos_libc.c` source contract (name says source).
- `test/01_unit/runtime/simple_core_process_contract_spec.spl` — `src/runtime/simple_core/core_*.spl` source contract.
- `test/01_unit/scripts/validate_mcp_native_smoke_source_spec.spl` — validates the SOURCE of `scripts/check/validate_mcp_native_smoke.spl` itself.
- `test/02_integration/app/spipe_process_harness_log_modes_spec.spl` — harness main.spl source shape (forbids `extern fn rt_file_read_text`).
- `test/02_integration/os/port/make_os_disk_fat32_integrity_spec.spl` — `scripts/os/make_os_disk.c` source contract; disk build lane.
- `test/02_integration/simpleos_driver_log_smoke_spec.spl` — asserts no `pass_todo` remains in null_block_driver source (ratchet on source text).
- `test/03_system/app/llm_caret/feature/llm_caret_messaging_plugin_runtime_spec.spl` — installed plugin/hook manifests + `src/app/llm_caret/messaging/cli.spl` deployment contract; needs installed plugin runtime.
- `test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl` — RV32 NVMe firmware AXI MMIO source contract; needs RV32 target.

ORA-001 pending/native scaffolds (pending behind FRs or need native binary/GPU/QEMU execution):
- `test/01_unit/os/compositor/engine2d_baremetal_rect_core_spec.spl` — baremetal rect core; no host-callable oracle.
- `test/01_unit/os/crypto/argon2d_kat_spec.spl` — `pending("argon2_native_runtime_helpers")`; RFC 9106 §5.1 vector exceeds interpreter watchdog by design.
- `test/01_unit/os/dma_driver_spec.spl`, `test/01_unit/os/driver_platform_spec.spl`, `test/01_unit/os/drivers/dma/direct_io_spec.spl`, `test/01_unit/os/kernel/arch/syscall_dispatch_spec.spl`, `test/01_unit/os/net_acceleration_spec.spl` — kernel/driver dispatch; need board/QEMU.
- `test/02_integration/lib/gpu/gpu_kernel_emission_spec.spl` — needs GPU kernel emission (CUDA/Vulkan present on host but emission lane is native-build gated).
- `test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl` — executes a CUDA binary; blocked same class.
- `test/02_integration/os/port/native_convergence_spec.spl` — native convergence lane.
- `test/02_integration/storage/dbfs/dbfs_no_regression_spec.spl` — no real executed assertion; DBFS regression lane needs native runtime.
- `test/03_system/app/simpleos/feature/simpleos_wine_dll_image_map_spec.spl`, `simpleos_wine_process_import_entrypoint_handoff_spec.spl` — Wine process lanes need Wine/QEMU.
- `test/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.spl` — blocked per `simpleos_wm_evidence_blocked_no_selfhosted_compiler_2026-08-20.md`.

Pre-existing RED at HEAD (proven via `git show HEAD:<spec>` restore, left RED, scores still fixed where only traceability was wrong):
- `test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl` — HEAD: `Results: 5 total, 0 passed, 5 failed`.
- `test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl` — HEAD: `Results: 3 total, 0 passed, 3 failed`.
- `test/03_system/app/os/feature/sosix_process_sharing_spec.spl` — HEAD: `Results: 6 total, 0 passed, 6 failed`.
