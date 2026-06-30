# Production GUI/web renderer parity evidence

> Validates the heavy production GUI/web renderer parity wrapper behavior that can be tested without launching the real renderer stack.

<!-- sdn-diagram:id=production_gui_web_renderer_parity_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=production_gui_web_renderer_parity_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

production_gui_web_renderer_parity_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=production_gui_web_renderer_parity_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Production GUI/web renderer parity evidence

Validates the heavy production GUI/web renderer parity wrapper behavior that can be tested without launching the real renderer stack.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/production_gui_web_renderer_parity_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the heavy production GUI/web renderer parity wrapper behavior that can
be tested without launching the real renderer stack.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test/03_system/check/production_gui_web_renderer_parity_evidence_spec.spl
```

## Acceptance

- A timed-out subcheck emits typed timeout evidence instead of leaving the
  wrapper without a status.
- The heavy wrapper resolves and exports a Simple binary for nested checks so a
  missing legacy cargo target does not hide renderer parity evidence.

## Scenarios

### Production GUI/web renderer parity evidence

#### exports resolved simple bin to nested production parity checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-production-gui-web-renderer-parity-evidence.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("for candidate in")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("command -v simple")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE")
expect(script).to_contain("production_gui_web_renderer_parity_simple_bin=$SIMPLE_BIN")
expect(script).to_contain("production_gui_web_renderer_parity_simple_bin_source=$SIMPLE_BIN_SOURCE")
```

</details>

#### selects repo bin simple before legacy cargo target simple

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-production-gui-web-backend-executed-evidence.shs")
expect(script).to_contain("SIMPLE_BIN_EXPLICIT=")
expect(script).to_contain("if [ -x \"bin/simple\" ]; then")
expect(script).to_contain("elif [ -x \"src/compiler_rust/target/release/simple\" ]; then")
expect(script).to_contain("elif have simple; then")
expect(script).to_contain("production_gui_backend_simple_bin=$SIMPLE_BIN")
expect(script.index_of("if [ -x \"bin/simple\" ]; then")).to_be_less_than(script.index_of("elif [ -x \"src/compiler_rust/target/release/simple\" ]; then"))
```

</details>

#### preserves explicit backend simple bin overrides in missing-bin evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-backend-explicit-missing && SIMPLE_BIN=build/test-production-gui-web-backend-explicit-missing/missing-simple BUILD_DIR=build/test-production-gui-web-backend-explicit-missing/out REPORT_PATH=build/test-production-gui-web-backend-explicit-missing/report.md sh scripts/check/check-production-gui-web-backend-executed-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-backend-explicit-missing/out/evidence.env")
expect(evidence).to_contain("production_gui_backend_status=unavailable")
expect(evidence).to_contain("production_gui_backend_reason=missing-simple-bin")
expect(evidence).to_contain("production_gui_backend_simple_bin=build/test-production-gui-web-backend-explicit-missing/missing-simple")
```

</details>

#### records bounded subcheck timeout evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-evidence-timeout && mkdir -p build/test-production-gui-web-renderer-parity-evidence-timeout/fixture && printf '#!/bin/sh\\nsleep 5\\n' > build/test-production-gui-web-renderer-parity-evidence-timeout/fixture/slow.sh && PRODUCTION_GUI_WEB_RENDERER_PARITY_MATRIX_SCRIPT=build/test-production-gui-web-renderer-parity-evidence-timeout/fixture/slow.sh PRODUCTION_GUI_WEB_RENDERER_PARITY_SUBCHECK_TIMEOUT_SECS=1 BUILD_ROOT=build/test-production-gui-web-renderer-parity-evidence-timeout/out REPORT_PATH=build/test-production-gui-web-renderer-parity-evidence-timeout/report.md sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-evidence-timeout/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_reason=electron-generated-gui-matrix-failed")
expect(evidence).to_contain("production_gui_web_renderer_parity_matrix_status=timeout")
expect(evidence).to_contain("production_gui_web_renderer_parity_matrix_reason=matrix-timeout")
expect(evidence).to_contain("production_gui_web_renderer_parity_matrix_timed_out=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_matrix_timeout_secs=1")
```

</details>

#### prints bounded summary output while keeping full evidence on disk

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-production-gui-web-renderer-parity-bounded-stdout"
val command = "rm -rf " + root + " && mkdir -p " + root + "/fixture && " +
    "printf '#!/bin/sh\\nmkdir -p \"$BUILD_ROOT\"\\nprintf \"electron_generated_gui_web_matrix_status=pass\\\\nelectron_generated_gui_web_matrix_reason=pass\\\\nelectron_generated_gui_web_matrix_verbose_marker=stored-only\\\\n\" > \"$BUILD_ROOT/evidence.env\"\\n' > " + root + "/fixture/matrix.sh && " +
    "printf '#!/bin/sh\\nmkdir -p \"$BUILD_DIR\"\\nprintf \"electron_simple_web_layout_manifest_status=fail\\\\nelectron_simple_web_layout_manifest_reason=fixture-layout-fail\\\\nelectron_simple_web_layout_manifest_verbose_marker=stored-only\\\\n\" > \"$BUILD_DIR/evidence.env\"\\nexit 1\\n' > " + root + "/fixture/layout.sh && " +
    "PRODUCTION_GUI_WEB_RENDERER_PARITY_MATRIX_SCRIPT=" + root + "/fixture/matrix.sh PRODUCTION_GUI_WEB_RENDERER_PARITY_LAYOUT_SCRIPT=" + root + "/fixture/layout.sh BUILD_ROOT=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs || true"
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("matrix_electron_generated_gui_web_matrix_verbose_marker=stored-only")
expect(evidence).to_contain("layout_electron_simple_web_layout_manifest_verbose_marker=stored-only")
expect(stdout).to_contain("production_gui_web_renderer_parity_status=fail")
expect(stdout).to_contain("production_gui_web_renderer_parity_layout_manifest_status=fail")
expect(stdout.contains("verbose_marker=stored-only")).to_equal(false)
expect(stdout.length()).to_be_less_than(800)
```

</details>

#### fails top-level parity when font offload is unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-font-unavailable && mkdir -p build/test-production-gui-web-renderer-parity-font-unavailable/fixture && printf '#!/bin/sh\\nmkdir -p \"$BUILD_ROOT\"\\nprintf \"electron_generated_gui_web_matrix_status=pass\\\\nelectron_generated_gui_web_matrix_reason=pass\\\\n\" > \"$BUILD_ROOT/evidence.env\"\\n' > build/test-production-gui-web-renderer-parity-font-unavailable/fixture/matrix.sh && printf '#!/bin/sh\\nmkdir -p \"$BUILD_DIR\"\\nprintf \"electron_simple_web_layout_manifest_status=pass\\\\nelectron_simple_web_layout_manifest_reason=pass\\\\nelectron_simple_web_layout_manifest_case_count=1\\\\nelectron_simple_web_layout_manifest_pass_count=1\\\\nelectron_simple_web_layout_manifest_tracked_count=0\\\\nelectron_simple_web_layout_manifest_fail_count=0\\\\n\" > \"$BUILD_DIR/evidence.env\"\\n' > build/test-production-gui-web-renderer-parity-font-unavailable/fixture/layout.sh && printf '#!/bin/sh\\nmkdir -p \"$BUILD_DIR\"\\nprintf \"tauri_chrome_simple_web_layout_manifest_status=pass\\\\ntauri_chrome_simple_web_layout_manifest_reason=pass\\\\ntauri_chrome_simple_web_layout_manifest_electron_capture_status=pass\\\\ntauri_chrome_simple_web_layout_manifest_host_uname_s=Darwin\\\\ntauri_chrome_simple_web_layout_manifest_host_uname_m=arm64\\\\ntauri_chrome_simple_web_layout_manifest_tauri_capture_status=pass\\\\ntauri_chrome_simple_web_layout_manifest_tauri_capture_reason=pass\\\\ntauri_chrome_simple_web_layout_manifest_tauri_capture_backend=macos-wkwebview-snapshot\\\\ntauri_chrome_simple_web_layout_manifest_tauri_capture_required_commands=swift,node\\\\ntauri_chrome_simple_web_layout_manifest_tauri_capture_missing_commands=\\\\ntauri_chrome_simple_web_layout_manifest_chrome_capture_status=pass\\\\ntauri_chrome_simple_web_layout_manifest_chrome_capture_reason=pass\\\\ntauri_chrome_simple_web_layout_manifest_chrome_capture_backend=chrome-live-bitmap\\\\ntauri_chrome_simple_web_layout_manifest_tauri_live_capture=true\\\\ntauri_chrome_simple_web_layout_manifest_chrome_live_capture=true\\\\ntauri_chrome_simple_web_layout_manifest_tauri_case_count=1\\\\ntauri_chrome_simple_web_layout_manifest_tauri_pass_count=1\\\\ntauri_chrome_simple_web_layout_manifest_tauri_tracked_count=0\\\\ntauri_chrome_simple_web_layout_manifest_tauri_fail_count=0\\\\ntauri_chrome_simple_web_layout_manifest_chrome_case_count=1\\\\ntauri_chrome_simple_web_layout_manifest_chrome_pass_count=1\\\\ntauri_chrome_simple_web_layout_manifest_chrome_tracked_count=0\\\\ntauri_chrome_simple_web_layout_manifest_chrome_fail_count=0\\\\ntauri_chrome_simple_web_layout_manifest_tauri_mismatch_count=0\\\\ntauri_chrome_simple_web_layout_manifest_chrome_mismatch_count=0\\\\ntauri_chrome_simple_web_layout_manifest_no_fake_capture=true\\\\ntauri_chrome_simple_web_layout_manifest_blur_or_tolerance_used=false\\\\n\" > \"$BUILD_DIR/evidence.env\"\\n' > build/test-production-gui-web-renderer-parity-font-unavailable/fixture/surface.sh && printf '#!/bin/sh\\nmkdir -p \"$BUILD_DIR\"\\nprintf \"production_gui_backend_status=pass\\\\nproduction_gui_backend_reason=pass\\\\nproduction_gui_backend_exact_backend_parity=true\\\\nproduction_gui_backend_cpu_simd_different_pixels=0\\\\nproduction_gui_backend_metal_resolved=metal\\\\nproduction_gui_backend_metal_different_pixels=0\\\\nproduction_gui_backend_metal_gpu_frame_complete=true\\\\nproduction_gui_backend_blur_or_tolerance_used=false\\\\nproduction_gui_backend_simple_bin=fixture-simple\\\\n\" > \"$BUILD_DIR/evidence.env\"\\n' > build/test-production-gui-web-renderer-parity-font-unavailable/fixture/backend.sh && printf '#!/bin/sh\\nmkdir -p \"$BUILD_DIR\"\\nprintf \"production_gui_font_offload_status=unavailable\\\\nproduction_gui_font_offload_reason=runtime-unavailable\\\\nproduction_gui_font_offload_vector_backend=metal\\\\nproduction_gui_font_offload_vector_status=runtime-unavailable\\\\nproduction_gui_font_offload_bitmap_backend=metal\\\\nproduction_gui_font_offload_bitmap_status=runtime-unavailable\\\\n\" > \"$BUILD_DIR/evidence.env\"\\n' > build/test-production-gui-web-renderer-parity-font-unavailable/fixture/font.sh && printf '#!/bin/sh\\nmkdir -p \"$BUILD_DIR\"\\nprintf \"metal_engine2d_framebuffer_readback_status=pass\\\\nmetal_engine2d_framebuffer_readback_reason=raw-metal-framebuffer-download-proven\\\\nmetal_engine2d_framebuffer_readback_spec_status=pass\\\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\\\n\" > \"$BUILD_DIR/evidence.env\"\\n' > build/test-production-gui-web-renderer-parity-font-unavailable/fixture/metal.sh && PRODUCTION_GUI_WEB_RENDERER_PARITY_MATRIX_SCRIPT=build/test-production-gui-web-renderer-parity-font-unavailable/fixture/matrix.sh PRODUCTION_GUI_WEB_RENDERER_PARITY_LAYOUT_SCRIPT=build/test-production-gui-web-renderer-parity-font-unavailable/fixture/layout.sh PRODUCTION_GUI_WEB_RENDERER_PARITY_SURFACE_SCRIPT=build/test-production-gui-web-renderer-parity-font-unavailable/fixture/surface.sh PRODUCTION_GUI_WEB_RENDERER_PARITY_BACKEND_SCRIPT=build/test-production-gui-web-renderer-parity-font-unavailable/fixture/backend.sh PRODUCTION_GUI_WEB_RENDERER_PARITY_FONT_OFFLOAD_SCRIPT=build/test-production-gui-web-renderer-parity-font-unavailable/fixture/font.sh PRODUCTION_GUI_WEB_RENDERER_PARITY_METAL_READBACK_SCRIPT=build/test-production-gui-web-renderer-parity-font-unavailable/fixture/metal.sh BUILD_ROOT=build/test-production-gui-web-renderer-parity-font-unavailable/out REPORT_PATH=build/test-production-gui-web-renderer-parity-font-unavailable/report.md sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-font-unavailable/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_reason=font-offload-evidence-failed")
expect(evidence).to_contain("production_gui_web_renderer_parity_font_offload_status=unavailable")
expect(evidence).to_contain("production_gui_web_renderer_parity_backend_simple_bin=fixture-simple")
```

</details>

#### records Metal readback evidence even when font offload is unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-production-gui-web-renderer-parity-font-fail-metal-pass"
val command = "rm -rf " + root + " && mkdir -p " + root + "/fixture && " +
    "printf '#!/bin/sh\\nmkdir -p \"$BUILD_ROOT\"\\nprintf \"electron_generated_gui_web_matrix_status=pass\\\\nelectron_generated_gui_web_matrix_reason=pass\\\\n\" > \"$BUILD_ROOT/evidence.env\"\\n' > " + root + "/fixture/matrix.sh && " +
    "printf '#!/bin/sh\\nmkdir -p \"$BUILD_DIR\"\\nprintf \"electron_simple_web_layout_manifest_status=pass\\\\nelectron_simple_web_layout_manifest_reason=pass\\\\nelectron_simple_web_layout_manifest_case_count=1\\\\nelectron_simple_web_layout_manifest_pass_count=1\\\\nelectron_simple_web_layout_manifest_tracked_count=0\\\\nelectron_simple_web_layout_manifest_fail_count=0\\\\n\" > \"$BUILD_DIR/evidence.env\"\\n' > " + root + "/fixture/layout.sh && " +
    "printf '#!/bin/sh\\nmkdir -p \"$BUILD_DIR\"\\nprintf \"tauri_chrome_simple_web_layout_manifest_status=pass\\\\ntauri_chrome_simple_web_layout_manifest_reason=pass\\\\ntauri_chrome_simple_web_layout_manifest_electron_capture_status=pass\\\\ntauri_chrome_simple_web_layout_manifest_tauri_capture_status=pass\\\\ntauri_chrome_simple_web_layout_manifest_chrome_capture_status=pass\\\\ntauri_chrome_simple_web_layout_manifest_tauri_live_capture=true\\\\ntauri_chrome_simple_web_layout_manifest_chrome_live_capture=true\\\\ntauri_chrome_simple_web_layout_manifest_tauri_case_count=1\\\\ntauri_chrome_simple_web_layout_manifest_tauri_pass_count=1\\\\ntauri_chrome_simple_web_layout_manifest_tauri_tracked_count=0\\\\ntauri_chrome_simple_web_layout_manifest_tauri_fail_count=0\\\\ntauri_chrome_simple_web_layout_manifest_chrome_case_count=1\\\\ntauri_chrome_simple_web_layout_manifest_chrome_pass_count=1\\\\ntauri_chrome_simple_web_layout_manifest_chrome_tracked_count=0\\\\ntauri_chrome_simple_web_layout_manifest_chrome_fail_count=0\\\\ntauri_chrome_simple_web_layout_manifest_tauri_mismatch_count=0\\\\ntauri_chrome_simple_web_layout_manifest_chrome_mismatch_count=0\\\\ntauri_chrome_simple_web_layout_manifest_no_fake_capture=true\\\\ntauri_chrome_simple_web_layout_manifest_blur_or_tolerance_used=false\\\\n\" > \"$BUILD_DIR/evidence.env\"\\n' > " + root + "/fixture/surface.sh && " +
    "printf '#!/bin/sh\\nmkdir -p \"$BUILD_DIR\"\\nprintf \"production_gui_backend_status=pass\\\\nproduction_gui_backend_reason=pass\\\\nproduction_gui_backend_exact_backend_parity=true\\\\nproduction_gui_backend_cpu_simd_different_pixels=0\\\\nproduction_gui_backend_metal_resolved=metal\\\\nproduction_gui_backend_metal_different_pixels=0\\\\nproduction_gui_backend_metal_gpu_frame_complete=true\\\\nproduction_gui_backend_blur_or_tolerance_used=false\\\\nproduction_gui_backend_simple_bin=fixture-simple\\\\n\" > \"$BUILD_DIR/evidence.env\"\\n' > " + root + "/fixture/backend.sh && " +
    "printf '#!/bin/sh\\nmkdir -p \"$BUILD_DIR\"\\nprintf \"production_gui_font_offload_status=unavailable\\\\nproduction_gui_font_offload_reason=runtime-unavailable\\\\n\" > \"$BUILD_DIR/evidence.env\"\\n' > " + root + "/fixture/font.sh && " +
    "printf '#!/bin/sh\\nmkdir -p \"$BUILD_DIR\"\\nprintf \"metal_engine2d_framebuffer_readback_status=pass\\\\nmetal_engine2d_framebuffer_readback_reason=raw-metal-framebuffer-download-proven\\\\nmetal_engine2d_framebuffer_readback_spec_status=pass\\\\nmetal_engine2d_framebuffer_gpu_readback_available=true\\\\nmetal_engine2d_framebuffer_blur_or_tolerance_used=false\\\\n\" > \"$BUILD_DIR/evidence.env\"\\n' > " + root + "/fixture/metal.sh && " +
    "PRODUCTION_GUI_WEB_RENDERER_PARITY_MATRIX_SCRIPT=" + root + "/fixture/matrix.sh PRODUCTION_GUI_WEB_RENDERER_PARITY_LAYOUT_SCRIPT=" + root + "/fixture/layout.sh PRODUCTION_GUI_WEB_RENDERER_PARITY_SURFACE_SCRIPT=" + root + "/fixture/surface.sh PRODUCTION_GUI_WEB_RENDERER_PARITY_BACKEND_SCRIPT=" + root + "/fixture/backend.sh PRODUCTION_GUI_WEB_RENDERER_PARITY_FONT_OFFLOAD_SCRIPT=" + root + "/fixture/font.sh PRODUCTION_GUI_WEB_RENDERER_PARITY_METAL_READBACK_SCRIPT=" + root + "/fixture/metal.sh BUILD_ROOT=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_reason=font-offload-evidence-failed")
expect(evidence).to_contain("production_gui_web_renderer_parity_font_offload_status=unavailable")
expect(evidence).to_contain("production_gui_web_renderer_parity_metal_readback_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_metal_readback_available=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_metal_readback_blur_or_tolerance_used=false")
```

</details>

#### forwards surface capture host and prerequisite evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-production-gui-web-renderer-parity-evidence-surface-context && mkdir -p build/test-production-gui-web-renderer-parity-evidence-surface-context/fixture && printf '#!/bin/sh\\nmkdir -p \"$BUILD_ROOT\"\\nprintf \"electron_generated_gui_web_matrix_status=pass\\\\nelectron_generated_gui_web_matrix_reason=pass\\\\n\" > \"$BUILD_ROOT/evidence.env\"\\n' > build/test-production-gui-web-renderer-parity-evidence-surface-context/fixture/matrix.sh && printf '#!/bin/sh\\nmkdir -p \"$BUILD_DIR\"\\nprintf \"electron_simple_web_layout_manifest_status=pass\\\\nelectron_simple_web_layout_manifest_reason=pass\\\\nelectron_simple_web_layout_manifest_case_count=50\\\\nelectron_simple_web_layout_manifest_pass_count=36\\\\nelectron_simple_web_layout_manifest_tracked_count=14\\\\nelectron_simple_web_layout_manifest_fail_count=0\\\\n\" > \"$BUILD_DIR/evidence.env\"\\n' > build/test-production-gui-web-renderer-parity-evidence-surface-context/fixture/layout.sh && printf '#!/bin/sh\\nmkdir -p \"$BUILD_DIR\"\\nprintf \"tauri_chrome_simple_web_layout_manifest_status=fail\\\\ntauri_chrome_simple_web_layout_manifest_reason=tauri-xvfb-run-unavailable\\\\ntauri_chrome_simple_web_layout_manifest_host_uname_s=Darwin\\\\ntauri_chrome_simple_web_layout_manifest_host_uname_m=arm64\\\\ntauri_chrome_simple_web_layout_manifest_electron_capture_status=pass\\\\ntauri_chrome_simple_web_layout_manifest_tauri_capture_status=unavailable\\\\ntauri_chrome_simple_web_layout_manifest_tauri_capture_reason=xvfb-run-unavailable\\\\ntauri_chrome_simple_web_layout_manifest_tauri_capture_backend=x11-xvfb-window-screenshot\\\\ntauri_chrome_simple_web_layout_manifest_tauri_capture_required_commands=cargo,xvfb-run,dbus-run-session,xdotool,import,convert,node\\\\ntauri_chrome_simple_web_layout_manifest_tauri_capture_missing_commands=xvfb-run,dbus-run-session,xdotool\\\\ntauri_chrome_simple_web_layout_manifest_tauri_live_capture=false\\\\ntauri_chrome_simple_web_layout_manifest_tauri_case_count=1\\\\ntauri_chrome_simple_web_layout_manifest_tauri_pass_count=0\\\\ntauri_chrome_simple_web_layout_manifest_tauri_tracked_count=0\\\\ntauri_chrome_simple_web_layout_manifest_tauri_fail_count=1\\\\ntauri_chrome_simple_web_layout_manifest_tauri_mismatch_count=0\\\\ntauri_chrome_simple_web_layout_manifest_chrome_capture_status=pass\\\\ntauri_chrome_simple_web_layout_manifest_chrome_capture_reason=pass\\\\ntauri_chrome_simple_web_layout_manifest_chrome_capture_backend=chrome-live-bitmap\\\\ntauri_chrome_simple_web_layout_manifest_chrome_live_capture=true\\\\ntauri_chrome_simple_web_layout_manifest_chrome_case_count=50\\\\ntauri_chrome_simple_web_layout_manifest_chrome_pass_count=36\\\\ntauri_chrome_simple_web_layout_manifest_chrome_tracked_count=14\\\\ntauri_chrome_simple_web_layout_manifest_chrome_fail_count=0\\\\ntauri_chrome_simple_web_layout_manifest_chrome_mismatch_count=0\\\\ntauri_chrome_simple_web_layout_manifest_no_fake_capture=true\\\\ntauri_chrome_simple_web_layout_manifest_blur_or_tolerance_used=false\\\\n\" > \"$BUILD_DIR/evidence.env\"\\nexit 1\\n' > build/test-production-gui-web-renderer-parity-evidence-surface-context/fixture/surface.sh && PRODUCTION_GUI_WEB_RENDERER_PARITY_MATRIX_SCRIPT=build/test-production-gui-web-renderer-parity-evidence-surface-context/fixture/matrix.sh PRODUCTION_GUI_WEB_RENDERER_PARITY_LAYOUT_SCRIPT=build/test-production-gui-web-renderer-parity-evidence-surface-context/fixture/layout.sh PRODUCTION_GUI_WEB_RENDERER_PARITY_SURFACE_SCRIPT=build/test-production-gui-web-renderer-parity-evidence-surface-context/fixture/surface.sh BUILD_ROOT=build/test-production-gui-web-renderer-parity-evidence-surface-context/out REPORT_PATH=build/test-production-gui-web-renderer-parity-evidence-surface-context/report.md sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-production-gui-web-renderer-parity-evidence-surface-context/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_reason=tauri-chrome-layout-manifest-failed")
expect(evidence).to_contain("production_gui_web_renderer_parity_surface_manifest_host_uname_s=Darwin")
expect(evidence).to_contain("production_gui_web_renderer_parity_surface_manifest_host_uname_m=arm64")
expect(evidence).to_contain("production_gui_web_renderer_parity_surface_manifest_tauri_capture_reason=xvfb-run-unavailable")
expect(evidence).to_contain("production_gui_web_renderer_parity_surface_manifest_tauri_capture_backend=x11-xvfb-window-screenshot")
expect(evidence).to_contain("production_gui_web_renderer_parity_surface_manifest_tauri_capture_required_commands=cargo,xvfb-run,dbus-run-session,xdotool,import,convert,node")
expect(evidence).to_contain("production_gui_web_renderer_parity_surface_manifest_tauri_capture_missing_commands=xvfb-run,dbus-run-session,xdotool")
expect(evidence).to_contain("production_gui_web_renderer_parity_surface_manifest_chrome_capture_reason=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_surface_manifest_chrome_capture_backend=chrome-live-bitmap")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/html_css_spec_traceability.md](doc/03_plan/sys_test/html_css_spec_traceability.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
