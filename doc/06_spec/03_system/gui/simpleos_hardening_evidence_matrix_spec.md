# SimpleOS Hardening Evidence Matrix Spec

> This scenario audits the current SimpleOS hardening goal as a requirement matrix. It does not replace the deeper live gates; it verifies that the current workspace has authoritative evidence for every explicit clause in the user request.

<!-- sdn-diagram:id=simpleos_hardening_evidence_matrix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_hardening_evidence_matrix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_hardening_evidence_matrix_spec -> std
simpleos_hardening_evidence_matrix_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_hardening_evidence_matrix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Hardening Evidence Matrix Spec

This scenario audits the current SimpleOS hardening goal as a requirement matrix. It does not replace the deeper live gates; it verifies that the current workspace has authoritative evidence for every explicit clause in the user request.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | .spipe/gui_hardening_current_plan/state.md |
| Plan | .spipe/gui_hardening_current_plan/state.md |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/gui/simpleos_hardening_evidence_matrix_spec.spl` |
| Updated | 2026-07-13 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This scenario audits the current SimpleOS hardening goal as a requirement
matrix. It does not replace the deeper live gates; it verifies that the current
workspace has authoritative evidence for every explicit clause in the user
request.

The matrix checks SSH transcript evidence, shared WM lifecycle evidence, CPU
SIMD Engine2D diagram evidence, layered WebRenderer/Engine2D bitmap evidence,
Simple GUI through WebRenderer bitmap evidence, host/QEMU WM counterpart
bitmap evidence, SimpleOS LLVM port evidence, and the latest live QEMU Simple
GUI/MDI framebuffer artifact. It also verifies the current GUI/Web/2D
Vulkan-backed RenderDoc aggregate evidence, the full Lean formal proof
integrity gate, the RISC-V/BYL dual-track formal gate, the focused critical
concurrency/resource formal gate, and the focused memory-safety formal gate.

## Acceptance Criteria

- Executable launch from the SimpleOS filesystem is proven by SSH serial and
  session transcript evidence for `/usr/bin/simple`, including listener,
  password auth, and exec-command markers.
- SSH server and shell launch both `/usr/bin/simple.smf` and `/usr/bin/simple`
  from the SimpleOS filesystem alias rather than a host fixed-command stub.
- Lean formal proof projects build through the shared proof checker and reject
  proof-trust bypasses.
- RISC-V generated RTL sidecars, BYL model facts, and manual Lean constraints
  pass the dual-track formal gate. Generated SBY/RVFI artifacts are still
  reported as readiness evidence, and the strict RTL/SBY proof row must pass
  when the SymbiYosys toolchain is present.
- Scheduler resource lifecycle, actor/channel backpressure, memory DRF,
  kernel-capability, and memory-capability theorem surfaces pass the focused
  critical formal gate.
- Process lifecycle resource cleanup, wait/reap state, and zombie/orphan
  invariants pass through an explicit formal matrix row.
- GC reachability, no-GC boundary, manual borrow, pointer borrow, and no-GC
  compile theorem surfaces pass the focused memory-safety formal gate.
- Hosted WM source and SimpleOS WM lifecycle behavior are covered by the shared
  WM renderer unification evidence report.
- CPU SIMD Engine2D diagram rendering has exact-bitmap mismatch count zero and
  no blur/tolerance policy.
- SimpleOS LLVM porting has current x86_64 cross clang compile/link smoke and
  aarch64 stage-2 cross-build evidence.
- GUI/Web/2D Vulkan RenderDoc evidence proves Simple, Chrome, and Electron
  `.rdc` captures with Vulkan browser backing and Linux render-log comparison.
- WebRenderer backed by Engine2D passes exact bitmap checks against Node and Bun
  counterparts, including the explicit `simple-web-engine2d-image-taskbar-command`
  sample page.
- Simple GUI backed by Simple WebRenderer passes exact Electron bitmap checks.
- Production GUI/WebRenderer parity passes the generated GUI matrix, Electron
  layout manifest, live Tauri/WebKitGTK and Chrome/Chromium surface manifest,
  and pure Simple Engine2D backend parity with zero mismatches and no
  blur/tolerance.
- QEMU WM capture and the host GTK GL scene counterpart both pass with zero
  mismatches and no blur/tolerance. Host GTK timing baselines are
  non-promoting, and guest-side Simple-vs-GTK performance is satisfied only by
  QEMU guest serial timing markers. If the guest-side performance gate is still
  blocked, the aggregate matrix is blocked and exits nonzero even when all
  artifact rows preserve their evidence fields.
- The live QEMU Simple GUI/MDI artifact has the expected 1024x768 PPM and raw
  pmemsave byte sizes, while the executable spec/manual require the canonical
  WM service-ready, integrated render-ready, MDI serial markers, input capture,
  and framebuffer anchor checks.
- The latest live QEMU Simple GUI/MDI PPM is parsed directly and must satisfy
  the same probe, header, body, top-lane, and taskbar pixel anchors as the live
  QMP capture spec.
- The RV64 display-smoke QMP report must use contract v2 and prove dynamic
  dimensions/stride, one correlated positive present revision, nonblack
  pixels, and at least four canonical desktop palette witnesses.
- Async/thread/process/coroutine regression evidence must be surfaced as a
  counted matrix row with the async hardening wrapper total, passed, failed,
  and missing counts.

## Examples

Run the matrix directly:

```bash
BUILD_DIR=build/simpleos_hardening_evidence_matrix_current \
REPORT_PATH=doc/09_report/simpleos_hardening_evidence_matrix_2026-06-05.md \
sh scripts/check/check-simpleos-hardening-evidence-matrix.shs
```

Run the SPipe gate:

```bash
SIMPLE_LIB=src src/compiler_rust/target/release/simple test \
  test/03_system/gui/simpleos_hardening_evidence_matrix_spec.spl \
  --mode=interpreter --clean --format json
```

## Failure Diagnostics

- A single failed row means the corresponding requirement lacks current
  evidence and should be rerun or repaired at its source gate.
- Failed runs emit `simpleos_hardening_matrix_blocked_rows` and
  `simpleos_hardening_matrix_recovery_hints` so handoff automation can route
  the missing evidence without parsing the report body.
- If `qemu_wm_simple_gui_mdi` fails only on artifact byte counts, rerun
  `test/03_system/gui/gui_entry_engine2d_wm_simple_web_spec.spl`.
- If layered GUI rows fail, rerun
  `test/03_system/gui/layered_simple_gui_web_engine2d_bitmap_evidence_spec.spl`.
- If SSH rows fail, rerun `test/03_system/ssh_live_login_in_qemu_spec.spl`.

## Matrix Rows

The wrapper emits these rows:

- `simpleos_hardening_mission_critical_release_status`
- `simpleos_hardening_mission_critical_release_blockers`
- `simpleos_hardening_mission_critical_prereqs_status`
- `simpleos_hardening_mission_critical_prereqs_missing`
- `simpleos_hardening_mission_critical_prereqs_next_action`
- `simpleos_hardening_nvme_baremetal_wrapper_coverage_status`
- `simpleos_hardening_nvme_baremetal_wrapper_coverage_blockers`
- `simpleos_hardening_nvme_baremetal_wrapper_rv32_self_test`
- `simpleos_hardening_nvme_baremetal_wrapper_rv32_spec_status`
- `simpleos_hardening_nvme_baremetal_wrapper_rv64_self_test`
- `simpleos_hardening_nvme_baremetal_wrapper_rv64_spec_status`
- `simpleos_hardening_async_library_hardening_status`
- `simpleos_hardening_async_library_hardening_gate`
- `simpleos_hardening_async_library_hardening_total`
- `simpleos_hardening_async_library_hardening_passed`
- `simpleos_hardening_async_library_hardening_failed`
- `simpleos_hardening_async_library_hardening_missing`
- `simpleos_hardening_exec_launch_fs_status`
- `simpleos_hardening_ssh_smf_exec_status`
- `simpleos_hardening_formal_lean_proofs_status`
- `simpleos_hardening_formal_riscv_dual_track_status`
- `simpleos_hardening_formal_critical_concurrency_status`
- `simpleos_hardening_formal_critical_concurrency_gate`
- `simpleos_hardening_formal_critical_concurrency_scope`
- `simpleos_hardening_formal_critical_concurrency_evidence`
- `simpleos_hardening_formal_memory_safety_status`
- `simpleos_hardening_formal_memory_safety_gate`
- `simpleos_hardening_formal_memory_safety_scope`
- `simpleos_hardening_formal_memory_safety_evidence`
- `simpleos_hardening_formal_storage_integrity_status`
- `simpleos_hardening_formal_storage_integrity_gate`
- `simpleos_hardening_formal_storage_integrity_scope`
- `simpleos_hardening_formal_storage_integrity_evidence`
- `simpleos_hardening_formal_boundary_integrity_status`
- `simpleos_hardening_formal_boundary_integrity_gate`
- `simpleos_hardening_formal_boundary_integrity_scope`
- `simpleos_hardening_formal_boundary_integrity_evidence`
- `simpleos_hardening_formal_process_resource_lifecycle_status`
- `simpleos_hardening_formal_process_resource_lifecycle_gate`
- `simpleos_hardening_formal_process_resource_lifecycle_scope`
- `simpleos_hardening_formal_process_resource_lifecycle_evidence`
- `simpleos_hardening_formal_coroutine_resource_bounds_status`
- `simpleos_hardening_formal_coroutine_resource_bounds_gate`
- `simpleos_hardening_formal_coroutine_resource_bounds_scope`
- `simpleos_hardening_formal_coroutine_resource_bounds_evidence`
- `simpleos_hardening_formal_compiler_language_status`
- `simpleos_hardening_formal_compiler_language_gate`
- `simpleos_hardening_formal_compiler_language_scope`
- `simpleos_hardening_formal_compiler_language_evidence`
- `simpleos_hardening_formal_ui_policy_status`
- `simpleos_hardening_formal_ui_policy_gate`
- `simpleos_hardening_formal_ui_policy_scope`
- `simpleos_hardening_formal_ui_policy_evidence`
- `simpleos_hardening_formal_coverage_status`
- `simpleos_hardening_formal_coverage_gate`
- `simpleos_hardening_formal_coverage_scope`
- `simpleos_hardening_formal_coverage_evidence`
- `simpleos_hardening_shared_wm_status`
- `simpleos_hardening_cpu_simd_status`
- `simpleos_hardening_llvm_port_status`
- `simpleos_hardening_gui_renderdoc_vulkan_status`
- `simpleos_hardening_web_renderer_engine2d_status`
- `simpleos_hardening_simple_gui_webrenderer_status`
- `simpleos_hardening_qemu_host_counterpart_status`
- `simpleos_hardening_qemu_gui_smf_artifact_status`
- `simpleos_hardening_qemu_mdi_status`
- `simpleos_hardening_rv64_display_smoke_qmp_status`
- `simpleos_hardening_qemu_virtio_gpu_access_status`
- `simpleos_hardening_qemu_host_gpu_2d_status`

The readiness matrix passes only when all twenty-six rows are `pass` and the
required guest-side QEMU performance release gate is `pass`. Mission-critical
release is a stricter gate: it still requires
`scripts/check/check-simpleos-mission-critical-release.shs` to pass, including
the strict RISC-V RTL SBY proof lane.

The host-GPU 2D wrapper is supplemental and does not change the 26-row count.
Set `SIMPLEOS_HOST_GPU_2D_LIVE=1` to run it, or provide
`SIMPLEOS_HOST_GPU_2D_REPORT`; otherwise the matrix reports `not-run`.

The report emits the counted `byl_sby_artifact_audit` row and the
`riscv_rtl_rvfi_readiness_note` so generated SBY/RVFI readiness artifacts cannot
be mistaken for a completed RTL proof pass.

## Evidence Sources

- SSH rows read `build/os/x64-ssh-live.serial.log`,
  `build/os/x64-ssh-live.session-smf.txt`, and
  `build/os/x64-ssh-live.session-exec.txt`.
- Formal proof rows run `scripts/check/check-lean-proofs.shs`.
- RISC-V/BYL formal rows run `scripts/check/check-riscv-formal-dual-track.shs`.
- Critical concurrency/resource rows run
  `scripts/check/check-simpleos-critical-formal-proofs.shs`.
- Memory-safety rows run
  `scripts/check/check-simpleos-memory-safety-formal-proofs.shs`.
- Storage/filesystem rows run
  `scripts/check/check-simpleos-storage-formal-proofs.shs`.
- Process/FFI/TLS boundary rows run
  `scripts/check/check-simpleos-boundary-formal-proofs.shs`.
- Compiler/language rows run
  `scripts/check/check-simpleos-compiler-language-formal-proofs.shs`.
- UI/policy/resource rows run
  `scripts/check/check-simpleos-ui-policy-formal-proofs.shs`.
- Formal coverage rows run `scripts/check/check-simpleos-formal-coverage.shs`.
- Async hardening rows run `scripts/check/check-async-library-hardening-evidence.shs`;
  scenario runs may provide `ASYNC_LIBRARY_HARDENING_LOG` to reuse the wrapper
  summary while direct matrix runs execute the wrapper.
- Shared WM reads
  `doc/09_report/shared_wm_renderer_unification_evidence_2026-07-05.md`.
- CPU SIMD reads `doc/09_report/cpu_simd_engine2d_evidence_current_2026-07-02.md`.
- LLVM port reads `doc/09_report/simpleos_llvm_port_evidence_current_2026-07-02.md`.
- GUI/Web/2D Vulkan RenderDoc reads
  `doc/09_report/gui_renderdoc_feature_coverage_status_2026-07-03.md`.
- Layered WebRenderer and Simple GUI rows read
  `doc/09_report/layered_simple_gui_web_engine2d_bitmap_evidence_2026-07-05.md`.
- The explicit sample-page WebRenderer row also reads
  `doc/09_report/simple_web_engine2d_js_bitmap_evidence_2026-07-03.md` and
  `doc/09_report/bun_simple_web_engine2d_js_bitmap_evidence_2026-07-05.md`.
- Host/QEMU counterpart evidence reads
  `doc/09_report/qemu_gtk_wm_capture_evidence_2026-07-05.md`.
- Production GUI/WebRenderer parity evidence reads the latest existing
  `doc/09_report/production_gui_web_renderer_parity_evidence_*.md` report
  unless `PRODUCTION_GUI_PARITY_REPORT` is set.
- QEMU MDI evidence reads the latest
  `build/tmp/gui_entry_engine2d_wm_simple_web_spec_*` capture directory plus
  `test/03_system/gui/gui_entry_engine2d_wm_simple_web_spec.spl` and its generated
  manual.
- RV64 display-smoke QMP evidence reads the current date-stamped contract-v2
  report unless `RV64_DISPLAY_SMOKE_REPORT` selects an explicit source report.

## Scope Notes

- This matrix is an audit gate, not a replacement for live QEMU or bitmap
  evidence generation.
- It intentionally requires exact bitmap/no blur/no tolerance report fields
  from the source gates.
- It intentionally distinguishes the explicit Simple Web sample-page evidence
  from the broader layered GUI scenes, because the hardening request names both
  a sample page and the full GUI/WebRenderer stack.
- It intentionally requires the latest MDI capture PPM and raw pmemsave byte
  sizes, because those prove a real 1024x768 framebuffer artifact exists.
- It samples the latest MDI PPM directly so a size-only artifact cannot satisfy
  the live QEMU row.
- The GUI SMF artifact contract is a counted matrix row. It cannot promote live
  QEMU capture or guest-side performance evidence, but a missing or failing
  SMF artifact contract keeps the matrix incomplete.
- QEMU guest perf can report `pass` only when the QEMU evidence report contains
  a harness pass, `sample_origin=qemu-guest`, and a serial marker line with
  `simple_frame_cycles` and `iterations` fields. The GTK timing is a host-side
  baseline field in the same report; it is not claimed as guest GTK evidence.
- If a report is stale or missing, the right fix is to rerun the source gate and
  refresh the report.
- If the matrix passes after a source gate was weakened, the source gate should
  be tightened; the matrix is only as strong as the row evidence it checks.
- Host GTK timing baselines are diagnostic by themselves and must never promote
  the `guest-simple-frame-plus-host-gtk-baseline` release gate without a real
  QEMU guest Simple frame marker.
- Production GUI/WebRenderer parity requires live Tauri and Chrome captures;
  `unavailable` browser-shell rows do not satisfy the Simple GUI/WebRenderer
  matrix row.
- Before release, run this readiness matrix together with the individual source
  gates that changed in the current branch, then run
  `scripts/check/check-simpleos-mission-critical-release.shs`. Mission-critical
  release evidence requires the strict SBY proof lane to pass and
  `release_blockers=none`.

**Requirements:** .spipe/gui_hardening_current_plan/state.md
**Plan:** .spipe/gui_hardening_current_plan/state.md
**Design:** N/A
**Research:** N/A

## Scenarios

### SimpleOS hardening evidence matrix

#### rejects a status-only cached host-GPU report

1. Validate the cached host-GPU report.
2. Report malformed evidence without promoting it.

The matrix invokes the canonical host-GPU wrapper's report validator. A file
containing only an overall `pass` and reason is classified as
`fail/malformed-wrapper-report`; it cannot stand in for the three correlated
Linux ISA receipts and their serial logs.

<details>
<summary>Executable SSpec</summary>

```simple
val run_id = _run_id()
val host_gpu_report = _host_gpu_report_path(run_id)
process_run_timeout("/bin/sh", ["-c", "mkdir -p " + _build_dir(run_id)], 5000)
step("Validate the cached host-GPU report")
expect(file_write(host_gpu_report,
    "simpleos_qemu_host_gpu_2d_status=pass\n" +
    "simpleos_qemu_host_gpu_2d_reason=all-linux-host-gpu-rows-pass\n"
)).to_be(true)
val result = _run_matrix_with_host_gpu_report(run_id, host_gpu_report)
step("Report malformed evidence without promoting it")
expect(result[2]).to_equal(0)
expect(result[0]).to_contain("simpleos_hardening_qemu_host_gpu_2d_status=fail")
expect(result[0]).to_contain("simpleos_hardening_qemu_host_gpu_2d_reason=malformed-wrapper-report")
```

</details>

#### passes the hardening matrix and mission-critical release gate with RTL/SBY prerequisites

<details>
<summary>Executable SSpec</summary>

Runnable source: 91 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val result = _run_matrix(run_id)
val stdout = result[0]
val stderr = result[1]
val code = result[2]
expect(code).to_equal(0)
expect(stdout).to_contain("simpleos_hardening_stale_reports=none")
expect(stdout).to_contain("simpleos_hardening_stale_report_names=none")
expect(stdout).to_contain("qemu_gtk_wm_capture_evidence_2026-07-05.md")
expect(stdout).to_contain("simpleos_hardening_matrix_status=pass")
expect(stdout).to_contain("simpleos_hardening_matrix_reason=pass")
expect(stdout).to_contain("simpleos_hardening_mission_critical_release_status=pass")
expect(stdout).to_contain("simpleos_hardening_mission_critical_release_blockers=none")
expect(stdout).to_contain("simpleos_hardening_mission_critical_prereqs_status=ready")
expect(stdout).to_contain("simpleos_hardening_mission_critical_prereqs_missing=none")
expect(stdout).to_contain("simpleos_hardening_mission_critical_prereqs_next_action=none")
expect(stdout).to_contain("simpleos_hardening_nvme_baremetal_wrapper_coverage_status=pass")
expect(stdout).to_contain("simpleos_hardening_nvme_baremetal_wrapper_coverage_blockers=none")
expect(stdout).to_contain("simpleos_hardening_nvme_baremetal_wrapper_rv32_self_test=pass")
expect(stdout).to_contain("simpleos_hardening_nvme_baremetal_wrapper_rv32_spec_status=pass")
expect(stdout).to_contain("simpleos_hardening_nvme_baremetal_wrapper_rv64_self_test=pass")
expect(stdout).to_contain("simpleos_hardening_nvme_baremetal_wrapper_rv64_spec_status=pass")
expect(stdout).to_contain("simpleos_hardening_async_library_hardening_status=pass")
expect(stdout).to_contain("simpleos_hardening_async_library_hardening_gate=scripts/check/check-async-library-hardening-evidence.shs")
expect(stdout).to_contain("simpleos_hardening_async_library_hardening_scope=regression gate for async primitives")
expect(stdout).to_contain("simpleos_hardening_async_library_hardening_evidence=19 async/thread/process/coroutine specs pass")
expect(stdout).to_contain("simpleos_hardening_async_library_hardening_total=19")
expect(stdout).to_contain("simpleos_hardening_async_library_hardening_passed=19")
expect(stdout).to_contain("simpleos_hardening_async_library_hardening_failed=0")
expect(stdout).to_contain("simpleos_hardening_async_library_hardening_missing=0")
expect(stdout).to_contain("simpleos_hardening_matrix_passed=26/26")
expect(stdout).to_contain("simpleos_hardening_matrix_blocked_rows=")
expect(stdout).to_contain("simpleos_hardening_exec_launch_fs_status=pass")
expect(stdout).to_contain("simpleos_hardening_ssh_smf_exec_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_lean_proofs_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_riscv_dual_track_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_critical_concurrency_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_critical_concurrency_gate=scripts/check/check-simpleos-critical-formal-proofs.shs")
expect(stdout).to_contain("simpleos_hardening_formal_critical_concurrency_scope=Lean model gate: kernel_scheduler, actor_channel, memory_model_drf, kernel_capabilities, memory_capabilities")
expect(stdout).to_contain("simpleos_hardening_formal_critical_concurrency_evidence=resource_acquire/release capacity, work stealing, task completion idempotence, bounded-channel backpressure, closed-channel wakeup/drain and buffered receive, DRF read/write and lock race constraints plus synchronized-safe variants, kernel capability default-deny, memory capability upgrade denial and unique/shared write constraints")
expect(stdout).to_contain("simpleos_hardening_formal_memory_safety_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_memory_safety_gate=scripts/check/check-simpleos-memory-safety-formal-proofs.shs")
expect(stdout).to_contain("simpleos_hardening_formal_memory_safety_scope=Lean model gate: gc_reachability, gc_boundary, gc_manual_borrow, manual_pointer_borrow, nogc_compile")
expect(stdout).to_contain("simpleos_hardening_formal_memory_safety_evidence=mark/sweep reachability invariant")
expect(stdout).to_contain("simpleos_hardening_formal_storage_integrity_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_storage_integrity_gate=scripts/check/check-simpleos-storage-formal-proofs.shs")
expect(stdout).to_contain("simpleos_hardening_formal_storage_integrity_scope=Lean model gate: db_storage, fat32, formal/nvfs")
expect(stdout).to_contain("simpleos_hardening_formal_storage_integrity_evidence=B-tree ordering/bounds")
expect(stdout).to_contain("simpleos_hardening_formal_boundary_integrity_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_boundary_integrity_gate=scripts/check/check-simpleos-boundary-formal-proofs.shs")
expect(stdout).to_contain("simpleos_hardening_formal_boundary_integrity_scope=Lean model gate: ffi_contract, process_lifecycle, tls_isolation")
expect(stdout).to_contain("simpleos_hardening_formal_boundary_integrity_evidence=FFI rejects undefined/null calls")
expect(stdout).to_contain("simpleos_hardening_formal_process_resource_lifecycle_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_process_resource_lifecycle_gate=scripts/check/check-simpleos-boundary-formal-proofs.shs")
expect(stdout).to_contain("simpleos_hardening_formal_process_resource_lifecycle_scope=Lean model gate: process_lifecycle resource cleanup")
expect(stdout).to_contain("simpleos_hardening_formal_process_resource_lifecycle_evidence=process_lifecycle proves exit_clears_resources")
expect(stdout).to_contain("simpleos_hardening_formal_coroutine_resource_bounds_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_coroutine_resource_bounds_gate=scripts/check/check-simpleos-critical-formal-proofs.shs + scripts/check/check-simpleos-memory-safety-formal-proofs.shs")
expect(stdout).to_contain("simpleos_hardening_formal_coroutine_resource_bounds_scope=Lean model gate: green-task coroutine lifecycle")
expect(stdout).to_contain("simpleos_hardening_formal_coroutine_resource_bounds_evidence=green-task coroutine lifecycle proves park/unpark")
expect(stdout).to_contain("simpleos_hardening_formal_compiler_language_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_compiler_language_gate=scripts/check/check-simpleos-compiler-language-formal-proofs.shs")
expect(stdout).to_contain("simpleos_hardening_formal_compiler_language_scope=Lean model gate: module_resolution, macro_auto_import, type_inference_compile, type_value_semantics, visibility_export")
expect(stdout).to_contain("simpleos_hardening_formal_compiler_language_evidence=module resolution ambiguity/exists rules")
expect(stdout).to_contain("simpleos_hardening_formal_ui_policy_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_ui_policy_gate=scripts/check/check-simpleos-ui-policy-formal-proofs.shs")
expect(stdout).to_contain("simpleos_hardening_formal_ui_policy_scope=Lean model gate: ui_compositor")
expect(stdout).to_contain("simpleos_hardening_formal_ui_policy_evidence=damage add preserves the new rect")
expect(stdout).to_contain("simpleos_hardening_formal_coverage_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_coverage_gate=scripts/check/check-simpleos-formal-coverage.shs")
expect(stdout).to_contain("simpleos_hardening_formal_coverage_scope=Formal coverage audit: Lean global gate, RISC-V dual track, critical concurrency/resource, memory safety, storage, boundary, process/resource lifecycle, coroutine/resource bounds, compiler/language, async-library hardening, and UI policy")
expect(stdout).to_contain("simpleos_hardening_formal_coverage_evidence=all SimpleOS hardening formal rows have executable wrapper gates, executed proof-checker, RISC-V dual-track, RTL/SBY, release-wrapper, NVMe baremetal wrapper coverage audit, async-library hardening wrapper, process/coroutine/resource theorem-wrapper self-tests, and matrix gate/scope fields; aggregate coverage cannot pass by status-only derivation")
expect(stdout).to_contain("simpleos_hardening_byl_sby_artifact_audit_status=pass")
expect(stdout).to_contain("simpleos_hardening_byl_sby_artifact_audit_gate=scripts/check/check-simpleos-byl-sby-artifacts.shs")
expect(stdout).to_contain("simpleos_hardening_byl_sby_artifact_audit_scope=checked-in non-Lean formal artifacts consist of the RISC-V BYL surface")
expect(stdout).to_contain("simpleos_hardening_byl_sby_artifact_audit_evidence=src/verification/riscv_product/riscv_product.byl")
expect(stdout).to_contain("simpleos_hardening_riscv_rtl_sby_proof_status=pass")
expect(stdout).to_contain("simpleos_hardening_riscv_rtl_sby_proof_log=")
expect(stdout).to_contain("simpleos_hardening_riscv_rtl_sby_proof_gate=scripts/check/check-riscv-rtl-sby-proof.shs")
expect(stdout).to_contain("simpleos_hardening_riscv_rtl_sby_proof_scope=strict RISC-V RTL SymbiYosys proof run for generated rv32/rv64 default and mlk bundles")
expect(stdout).to_contain("simpleos_hardening_riscv_rtl_sby_proof_blocker=none")
expect(stdout).to_contain("simpleos_hardening_riscv_rtl_rvfi_readiness_note=RISC-V generated RTL bundles pass RVFI port, formal harness, SBY, and manifest artifact checks through scripts/check/check-riscv-fpga-sidecar-contract.shs; without sby, yosys, and an SMT solver this is RVFI/SymbiYosys readiness evidence, not an RTL proof pass")
expect(stdout).to_contain("simpleos_hardening_shared_wm_status=pass")
expect(stdout).to_contain("simpleos_hardening_cpu_simd_status=pass")
expect(stdout).to_contain("simpleos_hardening_llvm_port_status=pass")
expect(stdout).to_contain("simpleos_hardening_llvm_port_report=doc/09_report/simpleos_llvm_port_evidence_current_2026-07-02.md")
expect(stdout).to_contain("simpleos_hardening_gui_renderdoc_vulkan_status=pass")
expect(stdout).to_contain("simpleos_hardening_gui_renderdoc_report=doc/09_report/gui_renderdoc_feature_coverage_status_2026-07-03.md")
expect(stdout).to_contain("simpleos_hardening_web_renderer_engine2d_status=pass")
expect(stdout).to_contain("simpleos_hardening_simple_gui_webrenderer_status=pass")
expect(stdout).to_contain("simpleos_hardening_production_gui_web_renderer_parity_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_host_counterpart_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_gui_smf_artifact_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_gui_smf_artifact_contract_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_gui_smf_artifact_contract_row=GUI_SMF_ARTIFACT_CONTRACT status=pass artifact=build/gui/pure_gui_hot.smf")
expect(stdout).to_contain(" qemu_status=pass")
expect(stdout).to_contain(" macos_status=not-run")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_release_gate=guest-simple-frame-plus-host-gtk-baseline")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_release_gate_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_release_blocker=none")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_harness_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_harness_reason=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_harness_sample_origin=qemu-guest")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_harness_required_sample_origin=qemu-guest")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_harness_marker_line=[desktop-e2e] qemu-perf sample_origin=qemu-guest simple_frame_cycles=")
expect(stdout).to_contain("simpleos_hardening_qemu_host_perf_promotes_qemu_perf=false")
expect(stdout).to_contain("simpleos_hardening_qemu_mdi_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_mdi_ppm_anchor_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_mdi_ppm_nonblack=")
expect(stdout).to_contain("simpleos_hardening_rv64_display_smoke_qmp_status=pass")
expect(stdout).to_contain("simpleos_hardening_rv64_display_smoke_qmp_contract_version=2")
expect(stdout).to_contain("simpleos_hardening_rv64_display_smoke_qmp_width=800")
expect(stdout).to_contain("simpleos_hardening_rv64_display_smoke_qmp_height=600")
expect(stdout).to_contain("simpleos_hardening_rv64_display_smoke_qmp_stride=3200")
expect(stdout).to_contain("simpleos_hardening_rv64_display_smoke_qmp_present_revision=7")
expect(stdout).to_contain("simpleos_hardening_rv64_display_smoke_qmp_palette_witnesses=5")
expect(stdout).to_contain("simpleos_hardening_gui_entry_capture_ppm_bytes=2359312")
expect(stdout).to_contain("simpleos_hardening_gui_entry_capture_raw_bytes=3145728")
val report = file_read(_report_path(run_id))
expect(report).to_contain("- status: pass")
expect(report).to_contain("- mission_critical_release_status: pass")
expect(report).to_contain("- mission_critical_release_blockers: none")
expect(report).to_contain("- reason: pass")
expect(report).to_contain("- blocked_rows:")
expect(report).to_contain("- stale_reports: none")
expect(report).to_contain("- stale_report_names: none")
expect(report).to_contain("- qemu_host_counterpart_bitmap: pass")
expect(report).to_contain("- qemu_guest_perf_release_gate_status: pass")
expect(report).to_contain("- qemu_guest_perf_release_blocker: none")
expect(report).to_contain("- mission_critical_release_gate: scripts/check/check-simpleos-mission-critical-release.shs")
expect(report).to_contain("- mission_critical_release_prereq_gate: scripts/check/check-simpleos-mission-critical-prereqs.shs")
expect(report).to_contain("- mission_critical_prereqs_status: ready")
expect(report).to_contain("- mission_critical_prereqs_missing: none")
expect(report).to_contain("- mission_critical_prereqs_next_action: none")
expect(report).to_contain("- nvme_baremetal_wrapper_coverage: pass")
expect(report).to_contain("- nvme_baremetal_wrapper_coverage_blockers: none")
expect(report).to_contain("- nvme_baremetal_wrapper_rv32_self_test: pass")
expect(report).to_contain("- nvme_baremetal_wrapper_rv32_spec_status: pass")
expect(report).to_contain("- nvme_baremetal_wrapper_rv64_self_test: pass")
expect(report).to_contain("- nvme_baremetal_wrapper_rv64_spec_status: pass")
expect(report).to_contain("- async_library_hardening: pass")
expect(report).to_contain("- async_library_hardening_gate: scripts/check/check-async-library-hardening-evidence.shs")
expect(report).to_contain("- async_library_hardening_scope: regression gate for async primitives")
expect(report).to_contain("- async_library_hardening_evidence: 19 async/thread/process/coroutine specs pass")
expect(report).to_contain("- async_library_hardening_total: 19")
expect(report).to_contain("- async_library_hardening_passed: 19")
expect(report).to_contain("- async_library_hardening_failed: 0")
expect(report).to_contain("- async_library_hardening_missing: 0")
expect(report).to_contain("- byl_sby_artifact_audit: pass")
expect(report).to_contain("- byl_sby_artifact_audit_gate: scripts/check/check-simpleos-byl-sby-artifacts.shs")
expect(report).to_contain("- byl_sby_artifact_audit_scope: checked-in non-Lean formal artifacts consist of the RISC-V BYL surface")
expect(report).to_contain("- byl_sby_artifact_audit_evidence: src/verification/riscv_product/riscv_product.byl")
expect(report).to_contain("- riscv_rtl_sby_proof_log: ")
expect(report).to_contain("- riscv_rtl_sby_proof_gate: scripts/check/check-riscv-rtl-sby-proof.shs")
expect(report).to_contain("- riscv_rtl_sby_proof_scope: strict RISC-V RTL SymbiYosys proof run for generated rv32/rv64 default and mlk bundles")
expect(report).to_contain("- riscv_rtl_sby_proof: pass")
expect(report).to_contain("- riscv_rtl_sby_proof_blocker: none")
expect(report).to_contain("- riscv_rtl_rvfi_readiness_note: RISC-V generated RTL bundles pass RVFI port, formal harness, SBY, and manifest artifact checks through scripts/check/check-riscv-fpga-sidecar-contract.shs; without sby, yosys, and an SMT solver this is RVFI/SymbiYosys readiness evidence, not an RTL proof pass")
expect(report).to_contain("- formal_lean_proofs: pass")
expect(report).to_contain("- formal_lean_proofs_log: ")
expect(report).to_contain("- formal_riscv_dual_track: pass")
expect(report).to_contain("- formal_riscv_dual_track_log: ")
expect(report).to_contain("- formal_critical_concurrency: pass")
expect(report).to_contain("- formal_critical_concurrency_log: ")
expect(report).to_contain("- formal_critical_concurrency_gate: scripts/check/check-simpleos-critical-formal-proofs.shs")
expect(report).to_contain("- formal_critical_concurrency_scope: Lean model gate: kernel_scheduler, actor_channel, memory_model_drf, kernel_capabilities, memory_capabilities")
expect(report).to_contain("- formal_critical_concurrency_evidence: resource_acquire/release capacity")
expect(report).to_contain("DRF read/write and lock race constraints")
expect(report).to_contain("- formal_memory_safety: pass")
expect(report).to_contain("- formal_memory_safety_log: ")
expect(report).to_contain("- formal_memory_safety_gate: scripts/check/check-simpleos-memory-safety-formal-proofs.shs")
expect(report).to_contain("- formal_memory_safety_scope: Lean model gate: gc_reachability, gc_boundary, gc_manual_borrow, manual_pointer_borrow, nogc_compile")
expect(report).to_contain("- formal_memory_safety_evidence: mark/sweep reachability invariant")
expect(report).to_contain("manual pointer valid-state/exclusive/shared borrow constraints")
expect(report).to_contain("- formal_storage_integrity: pass")
expect(report).to_contain("- formal_storage_integrity_log: ")
expect(report).to_contain("- formal_storage_integrity_gate: scripts/check/check-simpleos-storage-formal-proofs.shs")
expect(report).to_contain("- formal_storage_integrity_scope: Lean model gate: db_storage, fat32, formal/nvfs")
expect(report).to_contain("- formal_storage_integrity_evidence: B-tree ordering/bounds")
expect(report).to_contain("crash refinement")
expect(report).to_contain("- formal_boundary_integrity: pass")
expect(report).to_contain("- formal_boundary_integrity_log: ")
expect(report).to_contain("- formal_boundary_integrity_gate: scripts/check/check-simpleos-boundary-formal-proofs.shs")
expect(report).to_contain("- formal_boundary_integrity_scope: Lean model gate: ffi_contract, process_lifecycle, tls_isolation")
expect(report).to_contain("- formal_boundary_integrity_evidence: FFI rejects undefined/null calls")
expect(report).to_contain("TLS reads remain own-thread/key isolated")
expect(report).to_contain("- formal_process_resource_lifecycle: pass")
expect(report).to_contain("- formal_process_resource_lifecycle_log: ")
expect(report).to_contain("- formal_process_resource_lifecycle_gate: scripts/check/check-simpleos-boundary-formal-proofs.shs")
expect(report).to_contain("- formal_process_resource_lifecycle_scope: Lean model gate: process_lifecycle resource cleanup")
expect(report).to_contain("- formal_process_resource_lifecycle_evidence: process_lifecycle proves exit_clears_resources")
expect(report).to_contain("- formal_coroutine_resource_bounds: pass")
expect(report).to_contain("- formal_coroutine_resource_bounds_log: ")
expect(report).to_contain("- formal_coroutine_resource_bounds_gate: scripts/check/check-simpleos-critical-formal-proofs.shs + scripts/check/check-simpleos-memory-safety-formal-proofs.shs")
expect(report).to_contain("- formal_coroutine_resource_bounds_scope: Lean model gate: green-task coroutine lifecycle")
expect(report).to_contain("- formal_coroutine_resource_bounds_evidence: green-task coroutine lifecycle proves park/unpark")
expect(report).to_contain("- formal_compiler_language: pass")
expect(report).to_contain("- formal_compiler_language_log: ")
expect(report).to_contain("- formal_compiler_language_gate: scripts/check/check-simpleos-compiler-language-formal-proofs.shs")
expect(report).to_contain("- formal_compiler_language_scope: Lean model gate: module_resolution, macro_auto_import, type_inference_compile, type_value_semantics, visibility_export")
expect(report).to_contain("- formal_compiler_language_evidence: module resolution ambiguity/exists rules")
expect(report).to_contain("deterministic type inference")
expect(report).to_contain("- formal_ui_policy: pass")
expect(report).to_contain("- formal_ui_policy_log: ")
expect(report).to_contain("- formal_ui_policy_gate: scripts/check/check-simpleos-ui-policy-formal-proofs.shs")
expect(report).to_contain("- formal_ui_policy_scope: Lean model gate: ui_compositor")
expect(report).to_contain("- formal_ui_policy_evidence: damage add preserves the new rect")
expect(report).to_contain("recursive paint-order flatten")
expect(report).to_contain("- formal_coverage_log: ")
expect(report).to_contain("- formal_coverage_gate: scripts/check/check-simpleos-formal-coverage.shs")
expect(report).to_contain("- formal_coverage_scope: Formal coverage audit: Lean global gate, RISC-V dual track, critical concurrency/resource, memory safety, storage, boundary, process/resource lifecycle, coroutine/resource bounds, compiler/language, async-library hardening, and UI policy")
expect(report).to_contain("- formal_coverage_evidence: all SimpleOS hardening formal rows have executable wrapper gates, executed proof-checker, RISC-V dual-track, RTL/SBY, release-wrapper, NVMe baremetal wrapper coverage audit, async-library hardening wrapper, process/coroutine/resource theorem-wrapper self-tests, and matrix gate/scope fields; aggregate coverage cannot pass by status-only derivation")
```

</details>

#### fails closed when live QMP passes but GUI SMF artifact contract is not executed

- process run timeout
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val qemu_report = _qemu_report_path(run_id)
process_run_timeout("/bin/sh", ["-c", "mkdir -p " + _build_dir(run_id)], 5000)
expect(file_write(qemu_report,
    "# QEMU GTK WM Capture Evidence\n\n" +
    "- status: pass\n" +
    "- auto QMP status: pass\n" +
    "- qemu live bitmap status: pass\n" +
    "- live capture sample mismatches: 0\n" +
    "- live capture full-scene mismatches: 0\n" +
    "- qemu-side perf status: unavailable\n" +
    "- qemu-side perf release gate: guest-simple-frame-plus-host-gtk-baseline\n" +
    "- qemu-side perf required for release: true\n" +
    "- qemu-side perf release blocker: qemu-side-simple-perf-harness-not-wired\n" +
    "- qemu-side perf harness status: unwired\n" +
    "- qemu-side perf harness reason: qemu-side-simple-perf-harness-not-wired\n" +
    "- qemu-side perf harness sample origin: none\n" +
    "- qemu-side perf harness required sample origin: qemu-guest\n" +
    "- qemu-side perf harness marker line:\n" +
    "- host GTK GL WM scene mismatch count: 0\n" +
    "- host GTK GL WM scene blur/tolerance used: false\n" +
    "- host perf baseline status: pass\n" +
    "- host perf baseline comparison available: true\n" +
    "- host perf baseline promotes QEMU perf: false\n" +
    "- GUI SMF artifact contract status: fail\n" +
    "- GUI SMF artifact contract row: GUI_SMF_ARTIFACT_CONTRACT status=fail artifact=build/gui/pure_gui_hot.smf sha256=abc size=1 smf_role=2 arch=1 embedded_dynlib=true symbol=gui_dynlib_hot_probe_tick qemu_status=not-run qemu_reason=live-qemu-not-executed macos_status=not-run macos_reason=requires-macos-arm64\n"
)).to_equal(true)
val result = _run_matrix_with_qemu_report(run_id, qemu_report)
val stdout = result[0]
val code = result[2]
expect(code).to_equal(1)
expect(stdout).to_contain("simpleos_hardening_matrix_status=fail")
expect(stdout).to_contain("simpleos_hardening_matrix_reason=matrix-incomplete")
expect(stdout).to_contain("simpleos_hardening_matrix_blocked_rows=")
expect(stdout).to_contain("qemu_gui_smf_artifact_contract")
expect(stdout).to_contain("simpleos_hardening_matrix_recovery_hints=ssh=test/03_system/os/ssh_live_login_in_qemu_spec.spl")
expect(stdout).to_contain("simpleos_hardening_formal_lean_proofs_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_riscv_dual_track_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_critical_concurrency_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_memory_safety_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_storage_integrity_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_boundary_integrity_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_process_resource_lifecycle_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_coroutine_resource_bounds_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_compiler_language_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_ui_policy_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_coverage_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_host_counterpart_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_gui_smf_artifact_status=fail")
expect(stdout).to_contain("simpleos_hardening_production_gui_web_renderer_parity_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_gui_smf_artifact_contract_status=fail")
expect(stdout).to_contain("qemu_status=not-run")
expect(stdout).to_contain("macos_status=not-run")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_release_gate_status=blocked-unwired")
```

</details>

#### keeps the combined GUI SMF artifact row passing while stale reports block release

- process run timeout
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val qemu_report = _qemu_report_path(run_id)
process_run_timeout("/bin/sh", ["-c", "mkdir -p " + _build_dir(run_id)], 5000)
expect(file_write(qemu_report,
    "# QEMU GTK WM Capture Evidence\n\n" +
    "- status: pass\n" +
    "- auto QMP status: pass\n" +
    "- qemu live bitmap status: pass\n" +
    "- live capture sample mismatches: 0\n" +
    "- live capture full-scene mismatches: 0\n" +
    "- qemu-side perf status: pass\n" +
    "- qemu-side perf release gate: guest-simple-frame-plus-host-gtk-baseline\n" +
    "- qemu-side perf required for release: true\n" +
    "- qemu-side perf release blocker: none\n" +
    "- qemu-side perf harness status: pass\n" +
    "- qemu-side perf harness reason: pass\n" +
    "- qemu-side perf harness sample origin: qemu-guest\n" +
    "- qemu-side perf harness required sample origin: qemu-guest\n" +
    "- qemu-side perf simple frame cycles: 1000\n" +
    "- qemu-side perf host GTK frame us: 200\n" +
    "- qemu-side perf iterations: 30\n" +
    "- qemu-side perf timing unit: tsc\n" +
    "- qemu-side perf harness marker line: [desktop-e2e] qemu-perf sample_origin=qemu-guest simple_frame_cycles=1000 iterations=30 timing_unit=tsc\n" +
    "- host GTK GL WM scene mismatch count: 0\n" +
    "- host GTK GL WM scene blur/tolerance used: false\n" +
    "- host perf baseline status: pass\n" +
    "- host perf baseline comparison available: true\n" +
    "- host perf baseline promotes QEMU perf: false\n" +
    "- GUI SMF artifact contract status: pass\n" +
    "- GUI SMF artifact contract row: GUI_SMF_ARTIFACT_CONTRACT status=pass artifact=build/gui/pure_gui_hot.smf sha256=abc size=1 smf_role=2 arch=3 embedded_dynlib=true symbol=gui_dynlib_hot_probe_tick qemu_status=pass qemu_reason=live-qemu-artifact-verified macos_status=pass macos_reason=live-macos-window-artifact-verified\n"
)).to_equal(true)
val result = _run_matrix_with_qemu_report(run_id, qemu_report)
val stdout = result[0]
val code = result[2]
expect(code).to_equal(1)
expect(stdout).to_contain("simpleos_hardening_matrix_status=blocked")
expect(stdout).to_contain("simpleos_hardening_matrix_reason=stale-static-reports")
expect(stdout).to_contain("simpleos_hardening_stale_report_names=")
expect(stdout).to_contain("simpleos_hardening_matrix_passed=26/26")
expect(stdout).to_contain("simpleos_hardening_matrix_blocked_rows=stale_static_reports")
expect(stdout).to_contain("simpleos_hardening_qemu_host_counterpart_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_lean_proofs_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_riscv_dual_track_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_critical_concurrency_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_memory_safety_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_storage_integrity_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_boundary_integrity_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_process_resource_lifecycle_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_coroutine_resource_bounds_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_compiler_language_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_ui_policy_status=pass")
expect(stdout).to_contain("simpleos_hardening_formal_coverage_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_gui_smf_artifact_status=pass")
expect(stdout).to_contain("simpleos_hardening_production_gui_web_renderer_parity_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_gui_smf_artifact_contract_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_gui_smf_artifact_contract_row=GUI_SMF_ARTIFACT_CONTRACT status=pass artifact=build/gui/pure_gui_hot.smf")
expect(stdout).to_contain(" qemu_status=pass")
expect(stdout).to_contain(" macos_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_release_gate_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_release_blocker=none")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_harness_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_harness_sample_origin=qemu-guest")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_harness_marker_line=[desktop-e2e] qemu-perf sample_origin=qemu-guest simple_frame_cycles=1000 iterations=30 timing_unit=tsc")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [.spipe/gui_hardening_current_plan/state.md](.spipe/gui_hardening_current_plan/state.md)
- **Plan:** [.spipe/gui_hardening_current_plan/state.md](.spipe/gui_hardening_current_plan/state.md)


</details>
