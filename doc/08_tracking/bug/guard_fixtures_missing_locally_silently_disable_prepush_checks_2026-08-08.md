# Guard fixtures missing locally silently disable pre-push checks (2026-08-08)

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).
**Trigger:** `scripts/check/check-jit-closure-blockers.shs` fail-closed with
`ERROR — nothing was checked (selftest failed: 8)` because all 8 fixtures under
`test/fixtures/repro/compiler/jit_closure/` were absent from the shared working
copy while present on `origin/main`. Fail-closed worked; the concern is that a
fixture wipe can silently disable any guard that fail-OPENS.

## Method

- Guards enumerated: `ls scripts/check/*.shs` → **442**.
- Guards containing a selftest (`selftest` / `--self-test`): **79**
  (11 expose an explicit `--selftest` flag).
- Required inputs extracted per guard by scanning for repo-relative path
  literals (`test/ src/ doc/ scripts/ config/ tools/ proofs/`), then classified:
  - working copy: `test -e`
  - origin: membership in `git ls-tree -r --name-only origin/main` (111,658 entries)
- Additionally, every referenced *directory* was content-diffed against
  `origin/main` so a per-file wipe inside an intact fixture dir is caught (this
  is the check that found the real gaps; a dir-level `test -d` would have
  passed).

## Classification counts

| scope | rows | OK | MISSING-LOCALLY | ABSENT-EVERYWHERE |
|---|---|---|---|---|
| 79 selftest guards (path literals) | 715 | 632 | 0* | 79 |
| all 442 guards (path literals) | 2429 | 2081 | 0 | 348 |
| directory content-diff vs origin (all guards) | — | — | **4** | — |

\* Two apparent MISSING-LOCALLY hits (`formal/nvfs`, `gen/apple`) were regex
fragments of `src/verification/formal/nvfs` and
`tools/tauri-shell/src-tauri/gen/apple`, both present. Not real.

The 348 ABSENT-EVERYWHERE paths are overwhelmingly **synthetic paths the guards
create inside their own temp dirs** during selftest (`test/sub/*`,
`test/.spipe_gen/generated.spl`, `src/main.spl`, `test/report.md`,
`src/lib/first.spl`), plus report outputs under `doc/09_report/`. None is a
required tracked input. No real repo gap was found; nothing was created.

## Restored (already-tracked content, identical to origin — no landing needed)

All four are **symlinks** (git mode `120000`) that had been wiped from the
working copy; restored with `ln -s "$(git show origin/main:<path>)" <path>`:

| path | target |
|---|---|
| `test/01_unit/app/desugar/app` | `../../../../src/app` |
| `test/01_unit/lib/database/lib` | `../../../../src/lib` |
| `test/unit/app/desugar/app` | `../../../../src/app` |
| `test/unit/lib/database/lib` | `../../../../src/lib` |

The `jit_closure` fixture dir was already restored (9 fixtures present) before
this sweep ran; `check-jit-closure-blockers` now returns
`PASS — 615 file(s) scanned, 0 closure blockers`.

Re-verified at end of sweep: all 4 symlinks still present, jit_closure still 9
files. Nothing reverted during the session.

## Genuine FAILs on real content (do NOT silence)

| guard | verdict |
|---|---|
| `check-guard-wiring.shs` | `FAIL — 476 guard(s) checked, 48 unwired, 0 bad opt-out(s), 2 copied hook(s)` — 48 guards exist but are not wired into any hook/CI lane, i.e. they never run. This is the systemic version of the reported problem. |
| `check-test-tree-divergence.shs` | `FAIL — 982 diverged vs 982 baselined (1 new, 1 fixed-but-still-baselined)` |
| `check-lint-binary-staleness.shs` | `FAIL — deployed binary at bin/release/x86_64-unknown-linux-gnu/simple is STALE: missing 2 of 2 fresh marker(s): MEXH006 W-MC-RES-001` |
| `check-bootstrap-portability.shs` | `FAIL: retired Windows workflow restoration trigger missing` |
| `check-simpleos-formal-coverage.shs` | `FAIL: formal gate doc/07_guide/hardware/riscv/simple_generated_fpga_rtl.md missing text: release_blockers=none` |
| `check-vhdl-gen-probes.shs` / `check-vhdl-golden-match.shs` | `vhdl_gen_probes_ok=false` / `vhdl_golden_match_ok=false` |

Most other non-zero exits are environment-gated lanes (macOS host, GPU/Vulkan/
Metal/ROCm/CUDA device, QEMU images, built kernel ELF) and are expected red on
this Linux CPU host.

## Environment note

`git rev-parse --show-toplevel` in this shared clone returns
`/tmp/simple-stage4-codex.QM6dqU` (another session set `core.worktree`), and
`git` prints `warning: core.bare and core.worktree do not make sense`. Guards
anchor to their own script location, so they scanned
`/home/ormastes/dev/pub/simple` correctly; but any *ad-hoc* `git` command run
here resolves against the foreign worktree. Object-level commands
(`git ls-tree origin/main`, `git show origin/main:<path>`) are unaffected and
were used exclusively for this sweep.

## Recommended preflight (one line)

Run every selftest-bearing guard's selftest before trusting any push:

```sh
for g in $(grep -l -i 'selftest' scripts/check/*.shs); do sh "$g" --selftest >/dev/null 2>&1 || echo "GUARD NOT SELF-CLEAN: $g"; done
```

Guards without a `--selftest` flag should gain one; `check-guard-wiring.shs`
already reports the 48 guards that are unwired and should be treated as the
gating signal for recurrence.

## Full guard run table (verbatim final line, exit code)

Each guard was run as `sh scripts/check/<name>.shs 2>&1 | tail`. Guards whose
full scan exceeded the harness budget are marked `(TIMEOUT …)`; for those, the
last line emitted is quoted and is usually the selftest verdict, which had
already passed.

| guard | verbatim final line | exit |
|---|---|---|
| build-macos-es-history-collector.shs | scripts/check/build-macos-es-history-collector.shs: 81: /usr/bin/chflags: not found | 127 |
| build-macos-full-cli-gui-provenance.shs | macOS full CLI GUI provenance: FAIL (host-is-not-macos) | 1 |
| build-macos-gpu-2d-live-native.shs | usage: sh scripts/check/build-macos-gpu-2d-live-native.shs --build <vulkan|metal> | --verify <vulkan|metal> <manifest-snapshot> [canonical-origin] | --self-test-contract | 2 |
| build-simpleos-arm64-desktop-engine2d-attested.shs | arm64_desktop_engine2d_attested_build_reason=compiler-version-invalid | 1 |
| check-bootstrap-portability.shs | FAIL: retired Windows workflow restoration trigger missing | 1 |
| check-cache-identity-formal-proofs.shs | STATUS: PASS cache-identity-formal-proofs (build + 14 required theorems) | 0 |
| check-cuda-generated-2d-readback.shs | check-cuda-generated-2d-readback: PASS — 64 pixel(s) compared on device, 0 mismatch(es), reason=readback-pixels-matched | 0 |
| check-directx-native-readback.shs | report_path=doc/09_report/directx_native_readback_2026-08-08.md | 1 |
| check-extern-registration.shs | (scan exceeded harness budget; selftest line: detector did not find it. The registration scan is broken.) | 124 |
| check-generated-2d-backend-readback-matrix-evidence.shs | (scan exceeded harness budget; selftest line: ) | 124 |
| check-gpu-backend-layer-evidence.shs | gpu_backend_matrix status=SKIP_UNAVAILABLE backends=5 layers=20 unique=20 expected=20 pass=7 failures=0 skips=13 runtime=false | 0 |
| check-guard-wiring.shs | (scan exceeded harness budget; selftest line: check-guard-wiring: selftest 8/8 fixtures correct) | 124 |
| check-gui-renderdoc-feature-coverage-status.shs | (scan exceeded harness budget; selftest line: ) | 124 |
| check-gui-web-2d-headless-handoff-negative-selftest.shs | gui_web_2d_headless_handoff_negative_selftest_case_statuses=duplicate-gate:pass|gate-value:pass|host-count:pass|runbook-count:pass|proof-count:pass|host-value:pass|runbook-value:pass|proof-value:pass|host-format:pass|runbook-format:pass|proof-format:pass|host-gate-id:pass|runbook-gate-id:pass|proof-gate-id:pass | 0 |
| check-gui-web-2d-headless-handoff-prep.shs | (scan exceeded harness budget; selftest line: ) | 124 |
| check-jit-closure-blockers.shs | check-jit-closure-blockers: PASS — 615 file(s) scanned, 0 closure blockers (does NOT cover named-fn-ref miscompiles) | 0 |
| check-lean-proofs.shs | (scan exceeded harness budget; selftest line:   ...   building compiler_rust/lib/std) | 124 |
| check-lint-binary-staleness.shs | FAIL — deployed binary at bin/release/x86_64-unknown-linux-gnu/simple is STALE: missing 2 of 2 fresh marker(s): MEXH006 W-MC-RES-001 (present:) | 1 |
| check-lint-census.shs | ERROR: no targets given (use --self-test to check the classifier) | 2 |
| check-linux-hosted-wm-live-window-evidence.shs | linux_hosted_wm_live_window_snapshot=missing | 1 |
| check-local-gpu-perf-summary.shs | local_gpu_perf_summary_status=pass | 0 |
| check-metal-generated-2d-readback.shs | report_path=doc/09_report/metal_generated_2d_readback_2026-08-08.md | 1 |
| check-native-utf8-slice.shs | (scan exceeded harness budget; selftest line:        is expected to yield length 2 under the native raw-bytes policy.) | 124 |
| check-no-jit-module-drop.shs | (scan exceeded harness budget; selftest line: scanning 12994 file(s) — roots:src/lib src/app src/os src/compiler) | 124 |
| check-nvme-baremetal-wrapper-coverage.shs | STATUS: PASS nvme-baremetal-wrapper-coverage status=pass blockers=none | 0 |
| check-nvme-firmware-remaining-gates.shs | STATUS: POSTPONED cosmos-board BT-001..BT-006 | 0 |
| check-nvme-rv32-minimal-live.shs | (scan exceeded harness budget; selftest line: ) | 124 |
| check-opencl-generated-2d-readback.shs | report_path=doc/09_report/opencl_generated_2d_readback_2026-08-08.md | 0 |
| check-pinned-electron-resolver.shs | pinned-electron-resolver-self-test: expected --self-test | 1 |
| check-portable-compute-toolchains.shs | all_portable_compute_toolchains_verified=false | 0 |
| check-processing-ir-offload-break-even.shs | processing_ir_offload_ptx_source_hash_equal=true | 0 |
| check-processing-ir-vulkan-break-even.shs | processing_ir_vulkan_offload_source_hash_equal=true | 0 |
| check-production-gui-web-host-gpu-queue-readback-evidence.shs | (scan exceeded harness budget; selftest line: ) | 124 |
| check-renderdoc-simple-gate.shs | rdoc_simple_gate_required_owner_agreement_status=pass | 1 |
| check-riscv-formal-dual-track.shs | error: unknown command 'run' | 1 |
| check-riscv-fpga-sidecar-contract.shs | error: unknown command 'run' | 1 |
| check-riscv-rtl-sby-proof.shs | STATUS: FAIL riscv-rtl-sby-proof reason=sidecar-contract-failed gate=/home/ormastes/dev/pub/simple/scripts/check/check-riscv-fpga-sidecar-contract.shs | 1 |
| check-rocm-generated-2d-readback.shs | report_path=doc/09_report/rocm_generated_2d_readback_2026-08-08.md | 1 |
| check-runnable-probes.shs | (scan exceeded harness budget; selftest line:          defect classes an sspec describe block cannot observe.) | 124 |
| check-rv32-nvme-nand-recovery.shs | STATUS: PASS rv32-nvme-nand-recovery self-test | 0 |
| check-rv64-display-smoke-qmp-evidence.shs | (scan exceeded harness budget; selftest line: ) | 137 |
| check-seed-parse-superset.shs | (scan exceeded harness budget; selftest line: roots: src/compiler src/app src/lib src/runtime) | 124 |
| check-simple-2d-renderdoc-backend-equivalence.shs | simple_renderdoc_aggregate_requirements=REQ-001..REQ-021 | 1 |
| check-simpleos-boundary-formal-proofs.shs | STATUS: PASS simpleos-boundary-formal-proofs | 0 |
| check-simpleos-byl-sby-artifacts.shs | STATUS: PASS simpleos-byl-sby-artifacts | 0 |
| check-simpleos-compiler-language-formal-proofs.shs | STATUS: PASS simpleos-compiler-language-formal-proofs | 0 |
| check-simpleos-critical-formal-proofs.shs | STATUS: PASS simpleos-critical-formal-proofs — 85 theorem(s) checked across 5 Lake project(s) | 0 |
| check-simpleos-dbfs-root-qemu.shs | [dbfs-root-qemu] build it first (e.g. bin/simple os build --arch=x86_64) | 3 |
| check-simpleos-formal-coverage.shs | FAIL: formal gate doc/07_guide/hardware/riscv/simple_generated_fpga_rtl.md missing text: release_blockers=none | 1 |
| check-simpleos-hardening-evidence-matrix.shs | (scan exceeded harness budget; selftest line: simpleos_hardening_stale_report_names=shared_wm_renderer_unification_evidence_2026-07-05.md,cpu_simd_engine2d_evidence_current_2026-07-02.md,simpleos_llvm_port_evidence_current_2026-07-02.md,gui_renderdoc_feature_coverage_status_2026-07-03.md,layered_simple_gui_web_engine2d_bitmap_evidence_2026-07-05.md,production_gui_web_renderer_parity_evidence_2026-06-29.md,simple_web_engine2d_js_bitmap_evidence_2026-07-03.md,bun_simple_web_engine2d_js_bitmap_evidence_2026-07-05.md,qemu_gtk_wm_capture_evidence_2026-07-05.md) | 124 |
| check-simpleos-io-audio-qemu.shs | simpleos_io_audio_qemu_status=fail reason=guest-log-missing:x86_64:virtio-snd | 1 |
| check-simpleos-memory-safety-formal-proofs.shs | STATUS: PASS simpleos-memory-safety-formal-proofs | 0 |
| check-simpleos-mission-critical-prereqs.shs | STATUS: PASS simpleos-mission-critical-prereqs | 0 |
| check-simpleos-mission-critical-release.shs | (scan exceeded harness budget; selftest line: ) | 124 |
| check-simpleos-native-board-gpu-2d.shs | simpleos_native_board_gpu_exit_code=2 | 2 |
| check-simpleos-qemu-guest-gpu-passthrough.shs | simpleos_qemu_guest_gpu_passthrough_gpu_inventory=0000:0a:00.0:nvidia:16,0000:42:00.0:nvidia:26 | 0 |
| check-simpleos-qemu-host-gpu-2d.shs | simpleos_qemu_host_gpu_2d_reason=pure-simple-compiler-missing | 1 |
| check-simpleos-storage-formal-proofs.shs | STATUS: PASS simpleos-storage-formal-proofs | 0 |
| check-simpleos-ui-policy-formal-proofs.shs | STATUS: PASS simpleos-ui-policy-formal-proofs | 0 |
| check-simpleos-virtio-snd-qemu.shs | simpleos_virtio_snd_qemu_status=untestable reason=compiler-is-bootstrap-seed | 2 |
| check-simpleos-wm-qmp-drag-delta-evidence.shs | qemu_wm_drag_delta_drag_out=build/simpleos_wm_qmp_drag_delta_evidence/drag.out | 1 |
| check-simpleos-wm-visible-display-evidence.shs | (scan exceeded harness budget; selftest line: ) | 124 |
| check-simpleos-x86-kernel-elf.shs | [x86-kernel-elf] ERROR: usage: scripts/check/check-simpleos-x86-kernel-elf.shs ELF | --self-test | 1 |
| check-stage4-selfhost-parse-memory-multifile.shs | error=invalid_binary_path: | 2 |
| check-tauri-ios-mobile-mdi-evidence.shs | status=unavailable | 0 |
| check-tauri-mobile-mdi-evidence.shs | tauri_mobile_mdi_simple_bin_status=pass | 1 |
| check-test-tree-divergence.shs | check-test-tree-divergence: FAIL — 982 diverged vs 982 baselined (1 new, 1 fixed-but-still-baselined) | 1 |
| check-trait-solver-method-resolution-variant.shs | PASS — 11 file(s) checked (selftest: 3 fixtures) — try_trait_method_with_solver returns a MethodResolution enum VARIANT, and no struct-style MethodResolution(...) field bag exists under src/compiler | 0 |
| check-tree-size-push.shs | (scan exceeded harness budget; selftest line: check-tree-size-push: ERROR — nothing was checked (exit 2)) | 124 |
| check-ui-showcase-layering.shs | check-ui-showcase-layering: PASS — 10 file(s) checked in src/app/ui_showcase, 0 layering violation(s) (root /home/ormastes/dev/pub/simple) | 0 |
| check-utf8-slice-audit-live.shs | check-utf8-slice-audit-live: PASS — gate string present (3 occurrence(s)) and the self_test liveness violation fired (2 audit line(s)) in bin/release/x86_64-unknown-linux-gnu/simple | 0 |
| check-vacuous-specs.shs | (scan exceeded harness budget; selftest line: selftest: 8/8 fixtures behaved correctly (F1,F3,F4,F6 flagged; F2,F5,F7,F8 clean)) | 124 |
| check-vhdl-gen-probes.shs | vhdl_gen_probes_ok=false | 1 |
| check-vhdl-golden-match.shs | vhdl_golden_match_ok=false | 1 |
| check-vulkan-compiler-live-lane.shs | vulkan_compiler_live_lane_reason=compiler-producer-unset | 1 |
| check-vulkan-engine2d-readback.shs | overall=fail | 1 |
| check-webgpu-real-readback.shs | report_path=doc/09_report/webgpu_real_readback_2026-08-08.md | 1 |
| check-widget-showcase-4k-200fps.shs | gui_showcase_4k_200fps_time_log_file_status=fail | 1 |
| riscv-fpga-preflight-common.shs |  | 0 |

### Pre-push guards re-run without a scan timeout

| guard | verbatim final line | exit |
|---|---|---|
| check-tree-size-push.shs | check-tree-size-push: NOTHING TO PUSH — fd73bdc9047cf574583f27e6715fd2953139e20f..fd73bdc9047cf574583f27e6715fd2953139e20f is empty; NO COMMITS WERE CHECKED | 0 |
| check-no-conflict-tree-push.shs | check-no-conflict-tree-push: NOTHING TO PUSH — fd73bdc9047cf574583f27e6715fd2953139e20f..fd73bdc9047cf574583f27e6715fd2953139e20f is empty; NO COMMITS WERE CHECKED | 0 |
| check-no-conflict-markers-push.shs | check-no-conflict-markers-push: NOTHING TO PUSH — fd73bdc9047cf574583f27e6715fd2953139e20f..fd73bdc9047cf574583f27e6715fd2953139e20f is empty; NO FILES WERE CHECKED | 0 |
| check-guard-wiring.shs | check-guard-wiring: FAIL — 476 guard(s) checked, 48 unwired, 0 bad opt-out(s), 2 copied hook(s) | 1 |
| check-vacuous-specs.shs | (TIMEOUT 170s) selftest: 8/8 fixtures behaved correctly (F1,F3,F4,F6 flagged; F2,F5,F7,F8 clean) | 124 |
