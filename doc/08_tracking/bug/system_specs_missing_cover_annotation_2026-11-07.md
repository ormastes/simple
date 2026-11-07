# System specs missing `# @cover` block plain `simple test` (2026-11-07)

**Check:** `validate_system_test_covers` (`src/app/test_runner_new/test_runner_files.spl`)
flags every discovered file whose path contains `/system/` (excluding `/helpers/`,
`/fixtures/`) with no `# @cover <path> <pct>%` line before its first `use`/`describe`.
`test_runner_main.spl` then returns a failed summary (exit 3) unless `--unstable` or
`--no-cover-check` is given.

**Measured on origin/release/1.0.0:** 76 `*_spec.spl` files (124 counting non-spec
`.spl` under `/system/`). The reported figure of 639 was NOT reproduced from source;
`test/03_system/` paths do not contain the literal `/system/` and are not checked.
If 639 is observed again, capture the runner's printed list -- it may be a
miscompiled split/trim in the binary that ran the check.

**Fixed in this change:** 33 specs got a verified `@cover` target (each target exists).

**Still open (43):** no unambiguous `src/` target; adding a guessed one would be a
false coverage claim. Each needs an owner decision: name the real target, move the
spec out of `/system/` (e.g. pure-script/hardware gates), or delete a tautological spec.

| spec | reason |
|---|---|
| `test/system/app/compiler/feature/all_regions_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/app/compiler/feature/host_cpu_runtime_variants_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/app/compiler/feature/world_units_newunit_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/app/scv/feature/scv_storage_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/app/vscode_rich_editor/feature/vscode_rich_editor_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/c_parser_spec.spl` | src/lib/common/c_parser absent |
| `test/system/code_quality/bare_bool_lint_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/code_quality/chars_deprecated_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/code_quality/iter_deprecated_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/code_quality/live_kms_security_workflow_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/code_quality/warning_allow_root_cause_cleanup_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/compiler/lean_verification_workflow_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/compiler/parser_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/dap_protocol_live_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/database/sdn_checksum_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/exe_size_budget_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/hardware/riscv64_fpga/hardware_inventory_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/hardware/riscv64_fpga/hello_payload_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/hardware/riscv64_fpga/jtag_unbind_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/hardware/riscv64_fpga/manifest_format_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/hardware/riscv64_fpga/preflight_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/import_c_match_spec.spl` | c_name_match.spl absent under src |
| `test/system/infra/heavy_work_preflight_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/kv260_network_verification_gate_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/llm_hud_example_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/os_crypto_ref_signature_spec.spl` | signature_ffi under nogc_sync_mut absent; multi-variant, ambiguous |
| `test/system/os_rt_ed25519_sign_spec.spl` | signature_ffi under nogc_sync_mut absent; multi-variant, ambiguous |
| `test/system/os_rt_rsa_pss_verify_spec.spl` | signature_ffi under nogc_sync_mut absent; multi-variant, ambiguous |
| `test/system/os_tls_hosted_interop_mtls_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/qemu/os/appscan/arm_smf_appscan_qemu_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/qemu/os/appscan/riscv_smf_appscan_qemu_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/qemu/rv64gc_qemu_boot_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/simple_lsp_protocol_live_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/simpleos_guest_toolchain_wrapper_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/simpleos_reboot_live_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/simpleos_smp_ap_live_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/t32_terminal_power_remote_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/tools/deploy/smoke_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/ui/tui_web_render_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/ui/ui_access_contract_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/watcher/watcher_shb_wiring_compiled_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |
| `test/system/watcher/watcher_shb_wiring_system_spec.spl` | no single clear src target (shell/script/tautological/live/portable smoke) |

**Note:** `bare_bool_types_spec` covers `config_and_model.spl` only nominally; most of its tests exercise helpers defined in the spec itself.
