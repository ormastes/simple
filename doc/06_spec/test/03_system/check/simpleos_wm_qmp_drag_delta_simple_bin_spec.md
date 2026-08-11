# SimpleOS WM QMP Drag Delta Simple Binary Contract

> The live drag-delta check requires QEMU and a running SimpleOS desktop target, but its binary-selection contract can be verified without launching either. Rust seed overrides must fail before launch artifacts are produced.

<!-- sdn-diagram:id=simpleos_wm_qmp_drag_delta_simple_bin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wm_qmp_drag_delta_simple_bin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wm_qmp_drag_delta_simple_bin_spec -> std
simpleos_wm_qmp_drag_delta_simple_bin_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wm_qmp_drag_delta_simple_bin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

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
| Updated | 2026-07-06 |
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

#### selects self hosted Simple and records launcher provenance

<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(native_build_main).to_contain("cli_native_build(args)")
expect(native_build_main).to_contain("SIMPLE_NATIVE_BUILD_FORCE_WORKER")
expect(native_build_main).to_contain("[\"run\", \"src/app/cli/native_build_worker.spl\"]")
expect(native_build_main).to_contain("worker_args.push(\"--mode=interpreter\")")
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
val llvm_native_link = file_read("src/compiler/70.backend/backend/llvm_native_link.spl")
expect(llvm_native_link).to_contain("is_simpleos_x86_64_link")
expect(llvm_native_link).to_contain("link_simpleos_x86_64")
expect(llvm_native_link).to_contain("SIMPLE_NATIVE_BUILD_LINKER_SCRIPT")
expect(llvm_native_link).to_contain("examples/09_embedded/simple_os/arch/x86_64/linker.ld")
expect(llvm_native_link).to_contain("examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c")
```

</details>

#### rejects explicit Rust seed before SimpleOS QMP launch

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md](doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md)
- **Design:** [doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md](doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md)
- **Research:** [doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md](doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md)


</details>
