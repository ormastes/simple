# SimpleOS WM QMP Drag Delta Simple Binary Contract

> The live drag-delta check requires QEMU and a running SimpleOS desktop target, but its binary-selection contract can be verified without launching either. Rust seed overrides must fail before launch artifacts are produced.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS WM QMP Drag Delta Simple Binary Contract

The live drag-delta check requires QEMU and a running SimpleOS desktop target, but its binary-selection contract can be verified without launching either. Rust seed overrides must fail before launch artifacts are produced.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/simpleos_wm_qmp_drag_delta_simple_bin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The live drag-delta check requires QEMU and a running SimpleOS desktop target,
but its binary-selection contract can be verified without launching either.
Rust seed overrides must fail before launch artifacts are produced.

## Requirements

**Requirements:** N/A

- REQ-SIMPLEOS-QMP-BIN-001: Default Simple binary selection is self-hosted only.
- REQ-SIMPLEOS-QMP-BIN-002: Explicit Rust seed paths produce
  `simple-bin-forbidden` before SimpleOS/QMP launch.
- REQ-SIMPLEOS-QMP-BIN-003: Evidence output records selected Simple binary,
  source, and status fields.
- REQ-SIMPLEOS-QMP-DRAG-004: The x86 guest decodes signed PS/2 dx/dy bytes
  with bounded waits and routes the live pointer through the shared WM
  lifecycle window state.
- REQ-SIMPLEOS-QMP-DRAG-005: A drag receipt is emitted only from the lifecycle
  window's observed before/after geometry after a decoded button release.
- REQ-SIMPLEOS-QMP-DRAG-006: The QMP gate injects a relative 360,132 move to
  the Editor title bar followed by a -200,-52 drag and requires the resulting
  276,120 -> 76,68 geometry receipt.
- REQ-SIMPLEOS-QMP-DRAG-007: Rendering is committed once on release from the
  lifecycle window array rather than once per split PS/2 motion packet.

## Plan

**Plan:** doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and provenance fields.
3. Run the wrapper with a Rust seed `SIMPLE_BIN` override.
4. Confirm stdout and report show `simple-bin-forbidden`.
5. Confirm QMP launch and drag artifacts are not created.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates `SIMPLE_BIN` before launching the SimpleOS desktop QMP
target so invalid Rust seed overrides cannot masquerade as GUI/QMP evidence.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/simpleos_wm_qmp_drag_delta_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### SimpleOS WM QMP drag-delta Simple binary contract

#### routes decoded PS2 drag packets through real lifecycle geometry

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes decoded PS2 drag packets through real lifecycle geometry
   - Expected: entry does not contain `fn _shared_mdi_event_scene`
   - Expected: entry does not contain `window=2 from=276,120 to=76,68 focused=true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes decoded PS2 drag packets through real lifecycle geometry")
val entry = file_read("examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl")
expect(entry).to_contain("class QemuPs2MousePacket:")
expect(entry).to_contain("fn _poll_qemu_mouse_packet() -> QemuPs2MousePacket:")
expect(entry).to_contain("if (flags & 0x10) != 0:")
expect(entry).to_contain("if (flags & 0x20) != 0:")
expect(entry).to_contain("dx = dx - 256")
expect(entry).to_contain("dy = dy - 256")
expect(entry).to_contain("windows = moved.windows")
expect(entry).to_contain("interaction = moved.interaction")
expect(entry).to_contain("wm_lifecycle_pointer_move(")
expect(entry).to_contain("wm_lifecycle_left_button(interaction, false)")
expect(entry).to_contain("_present_mdi_lifecycle_scene_input_fb(scanout, windows, pointer_x, pointer_y)")
expect(entry).to_contain("from={drag_origin_x},{drag_origin_y} to={dragged.x},{dragged.y}")
expect(entry).to_contain("decoded_packets={pointer_packet_seq} render_commits=1")
expect(entry).to_contain("geometry_changed={geometry_changed}")
expect(entry.contains("fn _shared_mdi_event_scene")).to_equal(false)
expect(entry.contains("window=2 from=276,120 to=76,68 focused=true")).to_equal(false)

val script = file_read("scripts/check/check-simpleos-wm-qmp-drag-delta-evidence.shs")
expect(script).to_contain("hmp(f, \"mouse_move 360 132\")")
expect(script).to_contain("hmp(f, \"mouse_move -200 -52\")")
expect(script).to_contain("wait_drag_receipt")
expect(script).to_contain("classify_drag_geometry_receipt")
expect(script).to_contain("simpleos_wm_qmp_drag_delta_self_test=pass")
expect(script).to_contain("qemu_wm_drag_delta_guest_geometry_receipt_status=")
expect(script).to_contain("qemu_wm_drag_delta_guest_drag_from_x=")
expect(script).to_contain("qemu_wm_drag_delta_guest_drag_to_x=")
expect(script).to_contain("qemu_wm_drag_delta_drag_receipt_elapsed_ms=")
expect(script).to_contain("unexpected-or-unchanged-drag-geometry")
```

</details>

#### selects self hosted Simple and records launcher provenance

- selects self hosted Simple and records launcher provenance
   - Expected: native_build_main does not contain `return cli_native_build(args)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects self hosted Simple and records launcher provenance")
val script = file_read("scripts/check/check-simpleos-wm-qmp-drag-delta-evidence.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"$ROOT_DIR\"/bin/release/*/simple")
expect(script).to_contain("\"$ROOT_DIR\"/release/*/simple")
expect(script).to_contain("\"$ROOT_DIR\"/build/bootstrap/stage3/simple")
expect(script).to_contain("\"$ROOT_DIR\"/bin/simple")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("qemu_wm_drag_delta_simple_bin=")
expect(script).to_contain("qemu_wm_drag_delta_simple_bin_source=")
expect(script).to_contain("qemu_wm_drag_delta_simple_bin_status=")
expect(script).to_contain("src/app/test/simpleos_desktop_qmp_launch.spl --mode=interpreter --clean")
expect(script).to_contain("SIMPLE_OS_LOG_MODE=")
expect(script).to_contain(":-off")
expect(script).to_contain("guest-entry-not-reported")
expect(script).to_contain("wm-simple-web-build-timeout")
val native_build_main = file_read("src/app/cli/native_build_main.spl")
expect(native_build_main).to_end_with("    run_native_build_worker(args)\n")
expect(native_build_main.contains("return cli_native_build(args)")).to_equal(false)
expect(native_build_main).to_contain("[\"run\", \"src/app/cli/native_build_worker.spl\"]")
expect(native_build_main).to_contain("env_set(\"SIMPLE_EXECUTION_MODE\", \"interpret\")")
val runner_targets = file_read("src/os/_QemuRunner/runner_targets.spl")
expect(runner_targets).to_contain("fn _os_build_backend_for_target(target: OsTarget) -> text:")
expect(runner_targets).to_contain("output: \"build/os/simpleos_wm_simple_web_check_32.elf\"")
expect(runner_targets).to_contain("return \"llvm\"")
val compile_targets = file_read("src/app/io/_CliCompile/compile_targets.spl")
expect(compile_targets).to_contain("var build_mode = \"dynload\"")
expect(compile_targets).to_contain("if build_mode != \"dynload\" and build_mode != \"one-binary\"")
expect(compile_targets).to_contain("options.output_format = driver_output_format_both()")
expect(compile_targets).to_contain("options.output_format = driver_output_format_native()")
expect(compile_targets).to_contain("fn _native_build_entry_closure")
expect(compile_targets).to_contain("SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE")
expect(compile_targets).to_contain("SIMPLE_NATIVE_BUILD_TRACE_CLOSURE")
val native_build_worker = file_read("src/app/cli/native_build_worker.spl")
expect(native_build_worker).to_contain("use app.io._CliCompile.compile_targets.")
expect(native_build_worker).to_contain("cli_native_build")
val llvm_native_link = compiler_native_link_source()
expect(llvm_native_link).to_contain("is_simpleos_x86_64_link")
expect(llvm_native_link).to_contain("link_simpleos_x86_64")
expect(llvm_native_link).to_contain("SIMPLE_NATIVE_BUILD_LINKER_SCRIPT")
expect(llvm_native_link).to_contain("examples/09_embedded/simple_os/arch/x86_64/linker.ld")
expect(llvm_native_link).to_contain("examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c")
```

</details>

#### rejects explicit Rust seed before SimpleOS QMP launch

- rejects explicit Rust seed before SimpleOS QMP launch
   - Expected: code equals `0`
   - Expected: launch_code equals `0`
   - Expected: drag_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects explicit Rust seed before SimpleOS QMP launch")
val root = "build/test-simpleos-wm-qmp-drag-delta-seed-forbidden"
val command = "rm -rf " + root + " && mkdir -p " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-simpleos-wm-qmp-drag-delta-evidence.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run_timeout("/bin/sh", ["-c", command], 10000)
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("qemu_wm_drag_delta_status=fail")
expect(output).to_contain("qemu_wm_drag_delta_reason=simple-bin-forbidden")
expect(output).to_contain("qemu_wm_drag_delta_simple_bin=src/compiler_rust/target/release/simple")
expect(output).to_contain("qemu_wm_drag_delta_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(output).to_contain("qemu_wm_drag_delta_simple_bin_status=forbidden")

val report = file_read(root + "/report.md")
expect(report).to_contain("- reason: simple-bin-forbidden")
val (_launch_out, _launch_err, launch_code) = process_run_timeout("/bin/sh", ["-c", "test ! -f " + root + "/out/launch.out"], 5000)
expect(launch_code).to_equal(0)
val (_drag_out, _drag_err, drag_code) = process_run_timeout("/bin/sh", ["-c", "test ! -f " + root + "/out/drag.out"], 5000)
expect(drag_code).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md`
- **Design:** `doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md`
- **Research:** `doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-SIMPLEOS-QMP-BIN-001:`
- `REQ-SIMPLEOS-QMP-BIN-002:`
- `REQ-SIMPLEOS-QMP-BIN-003:`
- `REQ-SIMPLEOS-QMP-DRAG-004:`
- `REQ-SIMPLEOS-QMP-DRAG-005:`
- `REQ-SIMPLEOS-QMP-DRAG-006:`
- `REQ-SIMPLEOS-QMP-DRAG-007:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c12e5f68c97cbf4424718a4432b881fd89edde05680bd1fd7509a04590e2a2c6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c12e5f68c97cbf4424718a4432b881fd89edde05680bd1fd7509a04590e2a2c6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c12e5f68c97cbf4424718a4432b881fd89edde05680bd1fd7509a04590e2a2c6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/check/simpleos_wm_qmp_drag_delta_simple_bin_spec.spl
mirror: doc/06_spec/03_system/check/simpleos_wm_qmp_drag_delta_simple_bin_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/simpleos_wm_qmp_drag_delta_simple_bin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/simpleos_wm_qmp_drag_delta_simple_bin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/simpleos_wm_qmp_drag_delta_simple_bin_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/simpleos_wm_qmp_drag_delta_simple_bin_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes decoded PS2 drag packets through real lifecycle geometry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/simpleos_wm_qmp_drag_delta_simple_bin_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects self hosted Simple and records launcher provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/simpleos_wm_qmp_drag_delta_simple_bin_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects explicit Rust seed before SimpleOS QMP launch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
