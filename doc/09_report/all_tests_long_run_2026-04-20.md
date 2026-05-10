# All Tests Long Run - 2026-04-20

## Commands

- `bin/simple test --format text`
- `bin/simple test --only-skipped --format text`
- `bin/simple test --only-slow --format text`

## Results

- Full suite started and ran through long system/QEMU/DAP coverage, but did not complete cleanly. It stopped after the `gui_entry_engine2d_virtio_spec` watchdog timeout.
- `--only-skipped` passed, but exposed three `.skip` files that remain intentionally ignored by normal discovery:
  - `test/feature/mixin_spec.spl.skip`
  - `test/feature/static_polymorphism_spec.spl.skip`
  - `test/unit/runtime/runtime_value_test.spl.skip`
- `--only-slow` entered the same long system path and reached tracked `_tmp_x25519_*` probe failures before the foreground tool timeout. Those scratch probes were removed from the suite in the follow-up cleanup.

## Fixed In This Pass

- Removed crypto reference tests that passed by asserting `RefErr.Skipped`.
- Replaced them with real supported-vendor checks in `test/system/crypto_ref_harness_spec.spl`.
- Replaced several host-capability early-return tautologies with assertions against the build artifact or missing dependency condition.
- Fixed stale imports in `test/system/dap/dap_spec.spl`; the focused spec now passes.
- Fixed Bootstrap MCP tuple destructuring in `test/system/bootstrap_mcp_spec.spl`; the focused spec now passes.
- Removed tracked `test/system/_tmp_*` scratch probes that were being discovered as system tests.
- Updated `test/system/baremetal_test_runner_spec.spl` away from removed compile helpers; the focused spec now passes.
- Qualified sibling imports in `src/lib/nogc_sync_mut/test_runner/**` so externally imported test-runner modules do not fail on bare names like `test_runner_types`.
- Repaired the direct browser QEMU probe lanes by matching the x86_64 app-lane memory requirement; three of four focused `browser_engine_in_qemu_spec.spl` examples now pass.

## Major Remaining Failure Groups

- `test/system/browser_*_qemu*_spec.spl` and `test/system/gui_entry_*_spec.spl`: QEMU/guest boot, framebuffer, and watchdog failures.
  - Current fail-fast blocker: `test/system/browser_engine_in_qemu_spec.spl`. The browser probe, desktop probe, and browser software smoke examples pass; the full desktop wrapper still misses at least one required launcher/WM/browser marker.
- `test/system/compiler/ast_system_spec.spl`: generated branch coverage assertions fail for loop branches.
- `test/system/engine_2d_spec.spl`: engine scene graph, component, renderer, physics, input, resource, and signal expectations fail.
- `test/system/gui/*`: registry and WM pixel consistency semantic failures.
- `test/system/os_crypto_ref_signature_spec.spl`: targeted rerun still fails 13 signature examples; the no-op early-return branches were replaced, but the file is not clean.
- `test/lib/std/system/sdn/workflow_spec.spl`: stale imports were repaired, but the current SDN parser hangs on a minimal parse probe and the focused test times out.

## Status

STATUS: FAIL

The suite is not release-clean. The skipped crypto assertions were fixed, but the repository still has ignored `.skip` files and broad unrelated system failures.
