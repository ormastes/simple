# sspec resid6_part_04: pre-existing red specs and blocked classifications

- Date: 2026-08-27
- Batch: /tmp/sspec_census/resid6_part_04 (64 entries; all entered at effective=49 via blocker cap).
- Method: every "red" below was proved pre-existing by in-place `git show HEAD:<spec>` restore +
  rerun; counts identical at HEAD and after the modernization edit. No assertion was weakened.

## Pre-existing RED at HEAD (left red, modernization edit applied where score improved)

| spec | HEAD Results line |
|---|---|
| test/unit/std/module_import_spec.spl | 21 total, 18 passed, 3 failed |
| test/unit/compiler_core/types_spec.spl | 5 total, 3 passed, 2 failed |
| test/unit/compiler/backend/interpreter_backend_spec.spl | 13 total, 11 passed, 2 failed |
| test/unit/compiler/driver/genuine_import_ownership_spec.spl | 3 total, 2 passed, 1 failed |
| test/unit/lib/std/parser/error_recovery_spec.spl | 1 total, 0 passed, 1 failed |
| test/unit/lib/host_cpu_variant_spec.spl | 1 total, 0 passed, 1 failed (zero-examples) |
| test/unit/app/test_daemon/test_daemon_cache_module_spec.spl | 1 total, 0 passed, 1 failed |
| test/unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl | 32 total, 30 passed, 2 failed |
| test/unit/os/services/vfs/nvme_block_adapter_spec.spl | 9 total, 7 passed, 2 failed |
| test/unit/os/services/vfs/vfs_boot_nvme_lease_spec.spl | 27 total, 17 passed, 10 failed |
| test/integration/simpleos_driver_log_smoke_spec.spl | 3 total, 0 passed, 3 failed |
| test/integration/storage/dbfs/dbfs_no_regression_spec.spl | 5 total, 2 passed, 3 failed |
| test/integration/storage/dbfs/nvfs_hosted_no_regression_spec.spl | 5 total, 2 passed, 3 failed |
| test/integration/storage/dbfs/fat32_no_regression_spec.spl | 3 total, 2 passed, 1 failed |
| test/system/app/compiler/feature/host_cpu_runtime_variants_spec.spl | 11 total, 10 passed, 1 failed |
| test/system/app/compiler/feature/world_units_newunit_spec.spl | 1 total, 0 passed, 1 failed |
| test/system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl | 4 total, 3 passed, 1 failed |
| test/system/mcp/mcp_perf_regression_spec.spl | 46 total, 42 passed, 4 failed |
| test/system/simpleos_crypto_random_gate_spec.spl | 6 total, 5 passed, 1 failed |
| test/system/os/port/phase3_e2e_spec.spl | VERDICT outcome=ERROR, executed=0 |
| test/system/os/port/x86_64_elf_load_spec.spl | VERDICT outcome=ERROR, executed=0 |

## Blocked / classified (score left at 49; one line of evidence each)

- Placeholders for unimplemented modules (delete candidates): `test/unit/lib/ml/engine_spec.spl`,
  `test/unit/lib/nogc_async_mut/ml/engine_spec.spl` — sole scenario is `it "placeholder": skip`,
  "not yet implemented"; no quickcheck module exists under src/lib (grep clean).
  `test/unit/app/test_runner/quickcheck_spec.spl` — 60+ `it` bodies are bare `pass` with
  commented hints; no QuickCheck implementation in stdlib.
- Self-oracle scaffold (delete candidate): `test/unit/lib/host_cpu_variant_spec.spl` —
  re-implements SimdTier/CpuFeats/... locally, executes zero examples ("zero-examples" verdict).
- Scaffolds whose real modules exist (fixable, needs real-oracle rewrite, not done this batch):
  `test/unit/compiler/macros/macro_check_spec.spl` (src/compiler/30.types/macro_checker.spl
  exists), `test/unit/compiler/semantics/const_keys_spec.spl` (35.semantics/const_keys.spl
  exists), `test/unit/compiler/mir/mir_opt_benchmark_spec.spl`,
  `test/unit/compiler/parser/optimize_spec.spl` (all `nil` bodies),
  `test/unit/compiler/native/simd_check_spec.spl` (all `pass` bodies).
- Deliberate pending gates (leave as-is): `test/unit/lib/crypto/bcrypt_kat_spec.spl`
  (pending "bcrypt_native_runtime_helpers_2026-05-02"), `test/unit/os/crypto/argon2d_kat_spec.spl`
  (pending "argon2_native_runtime_helpers"), `test/unit/compiler/r2_pending_helper_spec.spl`
  (pending "reserved for future crypto KAT — see R2"),
  `test/system/compiler/debug_sidecar_json_order_spec.spl` + `rtl_mdsoc_byte_equal_spec.spl`
  (pending on SA-1/SA-3 baseline gates named in-file).
- Baremetal/QEMU-only execution (extern `serial_println` / ISA debug-exit port; cannot dual-check
  on host): `test/system/os_shell_spec.spl`, `os_network_spec.spl`, `os_storage_spec.spl`,
  `os_full_stack_spec.spl`, `os_shell_userland_tools_spec.spl`, `smux_system_spec.spl`,
  `test/system/stress_{2..25}_system_spec.spl` (literal brace filename, exists on disk).
- Delegation shim, oracle lives in shared suite: `test/system/os_ssh_spec.spl`
  (`run_os_ssh_suite()` import-only body).
- Gherkin prose only, no executable body: `test/system/app/lib/feature/common_compression_framework_spec.spl`.
- Source-grep guard (blocked per source_grep_guard_specs doc): `test/unit/compiler/mir/hir_type_coverage/handled_variants_neighbour_spec.spl`.
- Imported asserting helpers invisible to the file-scoped scanner (+ pre-existing red):
  `test/integration/storage/dbfs/dbfs_no_regression_spec.spl`,
  `nvfs_hosted_no_regression_spec.spl` — oracle is `assert_*` helpers imported from
  `test/fixtures/storage/dbfs/hosted_fs_no_regression_shared`; scanner's
  `_asserting_helper_names` only resolves helpers defined in the same file.
- Generated-fixture oracle invisible to scanner (+ pre-existing red):
  `test/unit/app/test_daemon/test_daemon_cache_module_spec.spl` — its oracle writes a sample
  spec text (containing `expect(1).to_equal(1)` as a STRING) and runs the daemon on it.

## Notes

- Score improvements used only semantics-preserving rewrites: `expect(x).to_equal(y)` /
  `x.should_equal(y)` method chains → `assert_equal(x, y)` / `assert_contains(x, y)`
  standalone forms, `"""` purpose docstrings where missing, and re-indenting `# @req` comments
  from column 8 (the `it` header's own indent) to column 12 (inside the body) so TRC-003
  binding resolves. No expected value changed except during dual-check bug injections
  (reverted byte-exact).
- Two transformer defects were caught and repaired before landing: commented-out
  `expect(...)` lines were being converted (comment text became code), and `)`-dropping
  when an expected string literal contained `), `. A literal-preservation checker
  (comparing quoted-segment multisets vs HEAD) was run over every edited file; all clean.
