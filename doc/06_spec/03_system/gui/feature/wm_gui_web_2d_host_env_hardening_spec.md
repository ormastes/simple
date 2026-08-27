# WM, GUI, Web, and 2D host-environment hardening

> Runs the production hosted-window evidence lane. The retained receipt must correlate one screen-originated event through WM and semantic Web dispatch to an application mutation and the same canonical Engine2D framebuffer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WM, GUI, Web, and 2D host-environment hardening

Runs the production hosted-window evidence lane. The retained receipt must correlate one screen-originated event through WM and semantic Web dispatch to an application mutation and the same canonical Engine2D framebuffer.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/wm_gui_web_2d_host_env_hardening.md and doc/02_requirements/nfr/wm_gui_web_2d_host_env_hardening.md |
| Plan | doc/03_plan/sys_test/wm_gui_web_2d_host_env_hardening.md |
| Design | doc/05_design/wm_gui_web_2d_host_env_hardening.md |
| Research | doc/01_research/local/wm_gui_web_2d_host_env_hardening.md and doc/01_research/domain/wm_gui_web_2d_host_env_hardening.md |
| Source | `test/03_system/gui/feature/wm_gui_web_2d_host_env_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Runs the production hosted-window evidence lane. The retained receipt must
correlate one screen-originated event through WM and semantic Web dispatch to
an application mutation and the same canonical Engine2D framebuffer.

Native x86, ARM, RISC-V, Vulkan, and RenderDoc rows are fail-closed. A blocked
row names its missing host prerequisite and exact resume command; it is never
reported as a pass.

**Requirements:** doc/02_requirements/feature/wm_gui_web_2d_host_env_hardening.md and doc/02_requirements/nfr/wm_gui_web_2d_host_env_hardening.md
**Plan:** doc/03_plan/sys_test/wm_gui_web_2d_host_env_hardening.md
**Design:** doc/05_design/wm_gui_web_2d_host_env_hardening.md
**Research:** doc/01_research/local/wm_gui_web_2d_host_env_hardening.md and doc/01_research/domain/wm_gui_web_2d_host_env_hardening.md

## Syntax

Run this spec with `SIMPLE_BIN` set to the deployed pure-Simple runtime after
the live-window and retained 4K evidence gates have populated their receipts.

## Scenarios

### production host event and render evidence

#### retains one correlated screen-to-Web-to-device frame receipt

- retains one correlated screen-to-Web-to-device frame receipt
   - Exec capture: after_step
- Inspect the real host capabilities
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: host_code equals `0`
- Inject one screen-originated event
   - Exec capture: after_step
- Follow the event through WM and GUI dispatch
   - Exec capture: after_step
- Render the resulting canonical composition
   - Exec capture: after_step
- Read back and compare the backend buffer
   - Exec capture: after_step
- Capture the Vulkan frame with RenderDoc
   - Exec capture: after_step
- Measure the retained rendering workload
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 76 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("retains one correlated screen-to-Web-to-device frame receipt")
step("Inspect the real host capabilities")
expect(file_exists(HOST_ENV_APP)).to_be(true)
val simple_bin = env_get("SIMPLE_BIN") ?? ""
expect(simple_bin == "").to_be(false)
val (host_stdout, _host_stderr, host_code) = process_run_timeout(
    simple_bin, ["run", HOST_ENV_APP, "--", "--format=json"], 120000)
expect(host_code).to_equal(0)
expect(host_stdout).to_contain("\"schema\":\"simple-test-host-env-v1\"")
expect(host_stdout).to_contain("\"name\":\"x86_simd\"")
expect(host_stdout).to_contain("\"name\":\"arm_simd\"")
expect(host_stdout).to_contain("\"name\":\"riscv_simd\"")
expect(host_stdout).to_contain("\"name\":\"vulkan\",\"status\":\"pass\"")
expect(host_stdout).to_contain("\"name\":\"renderdoc\",\"status\":\"pass\"")

step("Inject one screen-originated event")
expect(file_exists(LIVE_ENV)).to_be(true)
val live = file_read(LIVE_ENV)
expect(live).to_contain("linux_hosted_wm_live_window_status=pass")

step("Follow the event through WM and GUI dispatch")
expect(live).to_contain("linux_hosted_wm_live_window_focus_status=pass")
expect(live).to_contain("linux_hosted_wm_live_window_pointer_status=pass")
expect(live).to_contain("linux_hosted_wm_live_window_keyboard_status=pass")
expect(live).to_contain("linux_hosted_wm_live_window_text_status=pass")
expect(live).to_contain("linux_hosted_wm_live_window_event_origin=screen")
expect(live).to_contain("linux_hosted_wm_live_window_wm_target_id=")
expect(live).to_contain("linux_hosted_wm_live_window_input_compositor_wm_target_id=")
expect(live).to_contain("linux_hosted_wm_live_window_semantic_target_id=host-proof")
expect(live).to_contain("linux_hosted_wm_live_window_callback_count=1")
expect(live).to_contain("linux_hosted_wm_live_window_mutation_revision=1")
expect(live).to_contain("linux_hosted_wm_live_window_move_status=pass")
expect(live).to_contain("linux_hosted_wm_live_window_maximize_status=pass")
expect(live).to_contain("linux_hosted_wm_live_window_restore_status=pass")

step("Render the resulting canonical composition")
expect(live).to_contain("linux_hosted_wm_live_window_frame_marker=pass")
expect(live).to_contain("linux_hosted_wm_live_window_frame_correlation_status=pass")
expect(live).to_contain("linux_hosted_wm_live_window_input_composition_id=wm-composite")
expect(live).to_contain("linux_hosted_wm_live_window_input_web_content_image_count=")

step("Read back and compare the backend buffer")
expect(live).to_contain("linux_hosted_wm_live_window_framebuffer_status=pass")
expect(live).to_contain("linux_hosted_wm_live_window_input_readback_source=device_readback")
expect(live).to_contain("linux_hosted_wm_live_window_input_backend_handle=")
expect(live).to_contain("linux_hosted_wm_live_window_input_render_event_id=")
expect(live).to_contain("linux_hosted_wm_live_window_input_render_mutation_revision=")
expect(live).to_contain("linux_hosted_wm_live_window_input_readback_completed=true")
expect(live).to_contain("linux_hosted_wm_live_window_input_readback_width=1024")
expect(live).to_contain("linux_hosted_wm_live_window_input_readback_height=720")
expect(live).to_contain("linux_hosted_wm_live_window_input_readback_stride=4096")
expect(live).to_contain("linux_hosted_wm_live_window_input_readback_format=argb8888")
expect(live).to_contain("linux_hosted_wm_live_window_glyph_crop_live_match=true")
expect(live).to_contain("linux_hosted_wm_live_window_baseline_nonce=1")
expect(live).to_contain("linux_hosted_wm_live_window_input_nonce=2")
expect(live).to_contain("linux_hosted_wm_live_window_baseline_frame_checksum=")
expect(live).to_contain("linux_hosted_wm_live_window_input_frame_checksum=")
expect(live).to_contain("linux_hosted_wm_live_window_baseline_capture_sha256=")
expect(live).to_contain("linux_hosted_wm_live_window_input_capture_sha256=")
expect(live).to_contain("linux_hosted_wm_live_window_compatibility_fallback_status=pass")

step("Capture the Vulkan frame with RenderDoc")
expect(host_stdout).to_contain("\"name\":\"renderdoc\",\"status\":\"pass\"")
expect(file_read(HOST_ENV_APP)).to_contain("scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc-simple")

step("Measure the retained rendering workload")
expect(file_exists(PERF_ENV)).to_be(true)
val perf = file_read(PERF_ENV)
expect(perf).to_contain("gui_showcase_4k_200fps_status=pass")
expect(perf).to_contain("gui_showcase_4k_200fps_frames=200")
expect(perf).to_contain("gui_showcase_4k_200fps_readback_mode=argb-checksum")
expect(perf).to_contain("gui_showcase_4k_200fps_fallback_state=none")
expect(perf).to_contain("gui_showcase_4k_200fps_frame_p50_ns=")
expect(perf).to_contain("gui_showcase_4k_200fps_frame_p95_ns=")
expect(perf).to_contain("gui_showcase_4k_200fps_max_rss_kb=")
```

</details>

#### keeps the wrapper and app on existing production owners

- keeps the wrapper and app on existing production owners
- Verify the retained contract binds a forward Vulkan revision


<details>
<summary>Executable SSpec</summary>

Runnable source: 64 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the wrapper and app on existing production owners")
step("Verify the retained contract binds a forward Vulkan revision")
val wrapper = file_read(WRAPPER)
val app = file_read(HOST_ENV_APP)
val contract = file_read(HOST_ENV_CONTRACT)
val setup = file_read("scripts/setup/setup-gui-web-2d-vulkan-env.shs")
val browser_backing = file_read("scripts/check/gui-web-2d-vulkan-browser-backing-status.js")
val diff_argb = file_read("tools/pixel_compare/diff_argb.js")
val spec = file_read("test/03_system/gui/feature/wm_gui_web_2d_host_env_hardening_spec.spl")
expect(wrapper).to_contain("linux_hosted_wm_live_window")
expect(app).to_contain("host_simd_capability_row")
expect(app).to_contain("build/cpu-simd-engine2d-arch-matrix/aarch64/out/evidence.env")
expect(app).to_contain("build/cpu-simd-engine2d-arch-matrix/riscv64/out/evidence.env")
expect(app.contains("native_simd_pixel_evidence")).to_be(false)
expect(app).to_contain("build/gui-web-2d-vulkan-env-run-current/simple-vulkan-readback/evidence.env")
expect(app).to_contain("build/gui-web-2d-vulkan-env-run-current/evidence.env")
expect(app).to_contain("build/gui-web-2d-vulkan-env-browser-backing/evidence.env")
expect(app).to_contain("build/renderdoc/simple-gate/evidence.env")
expect(app).to_contain("build/linux-hosted-wm-live-window-evidence/evidence.env")
expect(app).to_contain("HostCapabilityRow")
expect(app).to_contain("host_capability_row_from_evidence")
expect(app).to_contain("file_exists(VULKAN_PATH) and file_exists(VULKAN_RUN_PATH) and file_exists(VULKAN_BROWSER_PATH)")
expect(app).to_contain("host_renderdoc_evidence_passes(renderdoc) and host_renderdoc_artifacts_are_current(renderdoc)")
expect(app).to_contain("host_vulkan_evidence_passes(vulkan) and host_browser_vulkan_parity_evidence_passes(vulkan_browser, vulkan_run)")
expect(app).to_contain("host_readback_evidence_passes(live) and host_readback_captures_are_current(live)")
expect(contract).to_contain("linux_hosted_wm_live_window_input_readback_source=device_readback")
expect(contract).to_contain("linux_hosted_wm_live_window_glyph_crop_live_match=true")
expect(contract).to_contain("host_display_input_evidence_passes(evidence)")
expect(contract).to_contain("linux_hosted_wm_live_window_baseline_capture_sha256")
expect(contract).to_contain("linux_hosted_wm_live_window_input_capture_sha256")
expect(contract).to_contain(
    "_host_evidence_values_increase(evidence, \"linux_hosted_wm_live_window_baseline_revision\", \"linux_hosted_wm_live_window_input_revision\")")
expect(contract).to_contain(
    "_host_evidence_value_matches(evidence, \"linux_hosted_wm_live_window_baseline_backend\", \"vulkan\")")
expect(contract).to_contain("fn host_browser_vulkan_parity_evidence_passes")
expect(contract).to_contain("gui_web_2d_vulkan_electron_browser_backing_source_file_status")
expect(contract).to_contain("gui_web_2d_vulkan_chrome_browser_backing_source_file_status")
expect(contract).to_contain("gui_web_2d_vulkan_electron_chrome_pairwise_diff_status")
expect(contract).to_contain("gui_web_2d_vulkan_electron_simple_pairwise_diff_status")
expect(contract).to_contain("gui_web_2d_vulkan_chrome_simple_pairwise_diff_status")
expect(contract).to_contain("gui_web_2d_vulkan_pixel_comparison_status")
expect(contract).to_contain("pixel_count == width * height")
expect(contract).to_contain("nonblank > 0 and nonblank <= pixel_count")
expect(contract).to_contain("gui_web_2d_vulkan_electron_browser_backing_browser_target_gpu_info_status")
expect(setup).to_contain("pixels.length === expectedPixelCount")
expect(setup).to_contain("const width = payload.width;")
expect(setup).to_contain("const height = payload.height;")
expect(setup.contains("const width = Number(payload.width")).to_be(false)
expect(setup).to_contain("nonblank > 0 && nonblank <= pixels.length")
expect(setup).to_contain("Number.isInteger(value) && value >= 0 && value <= 0xffffffff")
expect(setup).to_contain("for (let i = 0; pixelsValid && i < pixels.length; i += 1)")
expect(browser_backing).to_contain("electronBrowserGpuInfoStatus === \"pass\"")
expect(browser_backing).to_contain("const electronHardware = Boolean(electronAux.hardwareSupportsVulkan);")
expect(browser_backing.contains("electronAux.hardwareSupportsVulkan || electronAppAux.hardwareSupportsVulkan")).to_be(false)
expect(diff_argb).to_contain("ref.pixels.length !== total || test.pixels.length !== total")
expect(diff_argb).to_contain("Pixel array length mismatch")
expect(diff_argb).to_contain("Number.isInteger(value) && value >= 0 && value <= 0xFFFFFFFF")
expect(diff_argb).to_contain("!ref.pixels.every(validArgbPixel) || !test.pixels.every(validArgbPixel)")
expect(spec).to_contain("process_run_timeout(")
expect(spec).to_contain("120000")
expect(spec.contains("process_run(simple_bin")).to_be(false)
expect(app.contains("argb_mismatch_count=0")).to_be(false)
expect(contract).to_contain("val status = if evidence_present: \"fail\" else: \"blocked\"")
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

- **Requirements:** `doc/02_requirements/feature/wm_gui_web_2d_host_env_hardening.md and doc/02_requirements/nfr/wm_gui_web_2d_host_env_hardening.md`
- **Plan:** `doc/03_plan/sys_test/wm_gui_web_2d_host_env_hardening.md`
- **Design:** `doc/05_design/wm_gui_web_2d_host_env_hardening.md`
- **Research:** `doc/01_research/local/wm_gui_web_2d_host_env_hardening.md and doc/01_research/domain/wm_gui_web_2d_host_env_hardening.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dca2baf8ba376c5b90d14d1796baed8bea820afde579b5db0a3a6f046baa431c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dca2baf8ba376c5b90d14d1796baed8bea820afde579b5db0a3a6f046baa431c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dca2baf8ba376c5b90d14d1796baed8bea820afde579b5db0a3a6f046baa431c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/03_system/gui/feature/wm_gui_web_2d_host_env_hardening_spec.spl
mirror: doc/06_spec/03_system/gui/feature/wm_gui_web_2d_host_env_hardening_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/feature/wm_gui_web_2d_host_env_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/feature/wm_gui_web_2d_host_env_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/feature/wm_gui_web_2d_host_env_hardening_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
