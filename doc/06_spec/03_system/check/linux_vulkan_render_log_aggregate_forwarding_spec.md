# Linux Vulkan Render Log Aggregate Forwarding

> Verifies the lightweight contract that Linux Vulkan render-log diagnostics keep their structured blocker and per-gate fields visible at aggregate level. This spec reads wrapper source directly so it can run without a Linux GUI host, RenderDoc, Chrome, Electron, Vulkan, or the broad GUI aggregate fixture.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linux Vulkan Render Log Aggregate Forwarding

Verifies the lightweight contract that Linux Vulkan render-log diagnostics keep their structured blocker and per-gate fields visible at aggregate level. This spec reads wrapper source directly so it can run without a Linux GUI host, RenderDoc, Chrome, Electron, Vulkan, or the broad GUI aggregate fixture.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md |
| Source | `test/03_system/check/linux_vulkan_render_log_aggregate_forwarding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the lightweight contract that Linux Vulkan render-log diagnostics keep
their structured blocker and per-gate fields visible at aggregate level. This
spec reads wrapper source directly so it can run without a Linux GUI host,
RenderDoc, Chrome, Electron, Vulkan, or the broad GUI aggregate fixture.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/linux_vulkan_render_log_aggregate_forwarding_spec.spl --mode=interpreter --clean
```

## Acceptance

- The Linux Vulkan comparison wrapper emits blocked-gate count/list,
  per-gate statuses, RenderDoc artifact statuses, and host-tool readiness.
- The GUI RenderDoc aggregate reads and emits those same Linux fields.
- A Linux Vulkan row that otherwise says `pass` is rejected when
  `linux_vulkan_render_log_compare_blocked_gate_count` is not `0`.
- A forged zero blocker count cannot hide any failed per-gate status.

## Completion Criteria

This spec does not prove Linux Vulkan capture is complete. Goal completion
still requires a prepared Linux GUI host to produce:

- `linux_vulkan_render_log_compare_status=pass`
- `linux_vulkan_render_log_compare_blocked_gate_count=0`
- `linux_vulkan_render_log_compare_simple_vulkan_gate_status=pass`
- `linux_vulkan_render_log_compare_browser_backing_gate_status=pass`
- `linux_vulkan_render_log_compare_pairwise_gate_status=pass`
- `linux_vulkan_render_log_compare_argb_source_gate_status=pass`
- `linux_vulkan_render_log_compare_renderdoc_gate_status=pass`
- Simple, Chrome, and Electron RenderDoc artifact file statuses as `pass`
- Simple, Chrome, and Electron RenderDoc artifact magic as `RDOC`
- `gui_showcase_4k_200fps_status=pass`
- `gui_showcase_8k_perf_status=pass`

If a later Linux run lacks browser Vulkan backing, pairwise ARGB pixels, ARGB
source evidence, or real RDOC artifacts for Simple, Chrome, and Electron, keep
the aggregate incomplete and use the forwarded structured blockers instead of
parsing a summarized reason string.

## Scenarios

### Linux Vulkan render log aggregate forwarding

#### keeps structured Linux Vulkan blocker and gate fields in the aggregate contract

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps structured Linux Vulkan blocker and gate fields in the aggregate contract
- Read the Linux Vulkan comparison wrapper
- Assert the Linux wrapper emits blocked gates and per-gate statuses
- Read the GUI RenderDoc aggregate wrapper
- Assert the aggregate reads the Linux structured blocker fields
- Assert blocked Linux rows cannot pass aggregate validation
- Assert the aggregate emits the Linux structured gate fields
- Assert browser RenderDoc capture uses the detected tree and proven Vulkan flags
   - Expected: renderdoc_common does not contain `DefaultANGLEVulkan,VulkanFromANGLE`
   - Expected: renderdoc_common does not contain `score = NR`
- Assert delay-trigger shim catches ANGLE proc lookup for Vulkan
- Assert GPU autocapture evidence exposes frame-boundary hook counts
- Assert the RenderDoc guide documents lifecycle forwarding


<details>
<summary>Executable SSpec</summary>

Runnable source: 163 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps structured Linux Vulkan blocker and gate fields in the aggregate contract")
step("Read the Linux Vulkan comparison wrapper")
val linux_compare = file_read("scripts/check/check-linux-vulkan-render-log-compare.shs")

step("Assert the Linux wrapper emits blocked gates and per-gate statuses")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_blocked_gate_count\" \"$blocked_gate_count\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_blocked_gates\" \"$blocked_gates\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_simple_vulkan_gate_status\" \"$simple_vulkan_gate_status\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_browser_backing_gate_status\" \"$browser_backing_gate_status\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_pairwise_gate_status\" \"$pixel_gate_status\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_argb_source_gate_status\" \"$argb_source_gate_status\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_argb_checksum_reason\" \"$argb_checksum_reason\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_renderdoc_gate_status\" \"$renderdoc_gate_status\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_renderdoc_simple_artifact_file_status\" \"$simple_artifact_file_status\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_renderdoc_chrome_artifact_file_status\" \"$chrome_artifact_file_status\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_renderdoc_electron_artifact_file_status\" \"$electron_artifact_file_status\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_api\" \"$chrome_autocapture_api\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_started\" \"$chrome_autocapture_started\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_finished\" \"$chrome_autocapture_finished\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_start_source\" \"$chrome_autocapture_start_source\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_end_source\" \"$chrome_autocapture_end_source\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_renderdoc_electron_autocapture_api\" \"$electron_autocapture_api\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_renderdoc_electron_autocapture_started\" \"$electron_autocapture_started\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_renderdoc_electron_autocapture_finished\" \"$electron_autocapture_finished\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_renderdoc_electron_autocapture_start_source\" \"$electron_autocapture_start_source\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_renderdoc_electron_autocapture_end_source\" \"$electron_autocapture_end_source\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_host_renderdoc_status\" \"$host_renderdoc_status\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_host_chrome_status\" \"$host_chrome_status\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_host_electron_status\" \"$host_electron_status\"")

step("Read the GUI RenderDoc aggregate wrapper")
val aggregate = file_read("scripts/check/check-gui-renderdoc-feature-coverage-status.shs")

step("Assert the aggregate reads the Linux structured blocker fields")
expect(aggregate).to_contain("linux_vulkan_render_log_blocked_gate_count = value_of(\"linux_vulkan_render_log_compare_blocked_gate_count\"")
expect(aggregate).to_contain("linux_vulkan_render_log_blocked_gates = value_of(\"linux_vulkan_render_log_compare_blocked_gates\"")
expect(aggregate).to_contain("linux_vulkan_render_log_simple_vulkan_gate_status = value_of(\"linux_vulkan_render_log_compare_simple_vulkan_gate_status\"")
expect(aggregate).to_contain("linux_vulkan_render_log_browser_backing_gate_status = value_of(\"linux_vulkan_render_log_compare_browser_backing_gate_status\"")
expect(aggregate).to_contain("linux_vulkan_render_log_pairwise_gate_status = value_of(\"linux_vulkan_render_log_compare_pairwise_gate_status\"")
expect(aggregate).to_contain("linux_vulkan_render_log_argb_source_gate_status = value_of(\"linux_vulkan_render_log_compare_argb_source_gate_status\"")
expect(aggregate).to_contain("linux_vulkan_render_log_renderdoc_gate_status = value_of(\"linux_vulkan_render_log_compare_renderdoc_gate_status\"")
expect(aggregate).to_contain("linux_vulkan_render_log_renderdoc_chrome_autocapture_api = value_of(\"linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_api\"")
expect(aggregate).to_contain("linux_vulkan_render_log_renderdoc_chrome_autocapture_started = value_of(\"linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_started\"")
expect(aggregate).to_contain("linux_vulkan_render_log_renderdoc_chrome_autocapture_finished = value_of(\"linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_finished\"")
expect(aggregate).to_contain("linux_vulkan_render_log_renderdoc_chrome_autocapture_start_source = value_of(\"linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_start_source\"")
expect(aggregate).to_contain("linux_vulkan_render_log_renderdoc_chrome_autocapture_end_source = value_of(\"linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_end_source\"")
expect(aggregate).to_contain("linux_vulkan_render_log_renderdoc_electron_autocapture_api = value_of(\"linux_vulkan_render_log_compare_renderdoc_electron_autocapture_api\"")
expect(aggregate).to_contain("linux_vulkan_render_log_renderdoc_electron_autocapture_started = value_of(\"linux_vulkan_render_log_compare_renderdoc_electron_autocapture_started\"")
expect(aggregate).to_contain("linux_vulkan_render_log_renderdoc_electron_autocapture_finished = value_of(\"linux_vulkan_render_log_compare_renderdoc_electron_autocapture_finished\"")
expect(aggregate).to_contain("linux_vulkan_render_log_renderdoc_electron_autocapture_start_source = value_of(\"linux_vulkan_render_log_compare_renderdoc_electron_autocapture_start_source\"")
expect(aggregate).to_contain("linux_vulkan_render_log_renderdoc_electron_autocapture_end_source = value_of(\"linux_vulkan_render_log_compare_renderdoc_electron_autocapture_end_source\"")
expect(aggregate).to_contain("linux_vulkan_render_log_host_renderdoc_status = value_of(\"linux_vulkan_render_log_compare_host_renderdoc_status\"")
expect(aggregate).to_contain("linux_vulkan_render_log_host_chrome_status = value_of(\"linux_vulkan_render_log_compare_host_chrome_status\"")
expect(aggregate).to_contain("linux_vulkan_render_log_host_electron_status = value_of(\"linux_vulkan_render_log_compare_host_electron_status\"")

step("Assert blocked Linux rows cannot pass aggregate validation")
expect(aggregate).to_contain("elif linux_vulkan_render_log_blocked_gate_count != \"0\":")
expect(aggregate).to_contain("linux_vulkan_render_log_reason = \"linux-vulkan-blocked-gates-present:\"")
expect(aggregate).to_contain("elif linux_vulkan_render_log_simple_vulkan_gate_status != \"pass\":")
expect(aggregate).to_contain("elif linux_vulkan_render_log_browser_backing_gate_status != \"pass\":")
expect(aggregate).to_contain("elif linux_vulkan_render_log_pairwise_gate_status != \"pass\":")
expect(aggregate).to_contain("elif linux_vulkan_render_log_argb_source_gate_status != \"pass\":")
expect(aggregate).to_contain("linux_vulkan_render_log_reason = \"linux-vulkan-argb-source-gate-not-pass:\"")
expect(aggregate).to_contain("elif linux_vulkan_render_log_renderdoc_gate_status != \"pass\":")

step("Assert the aggregate emits the Linux structured gate fields")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_blocked_gate_count\", linux_vulkan_render_log_blocked_gate_count)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_blocked_gates\", linux_vulkan_render_log_blocked_gates)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_simple_vulkan_gate_status\", linux_vulkan_render_log_simple_vulkan_gate_status)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_browser_backing_gate_status\", linux_vulkan_render_log_browser_backing_gate_status)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_pairwise_gate_status\", linux_vulkan_render_log_pairwise_gate_status)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_argb_source_gate_status\", linux_vulkan_render_log_argb_source_gate_status)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_gate_status\", linux_vulkan_render_log_renderdoc_gate_status)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_api\", linux_vulkan_render_log_renderdoc_chrome_autocapture_api)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_started\", linux_vulkan_render_log_renderdoc_chrome_autocapture_started)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_finished\", linux_vulkan_render_log_renderdoc_chrome_autocapture_finished)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_start_source\", linux_vulkan_render_log_renderdoc_chrome_autocapture_start_source)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_end_source\", linux_vulkan_render_log_renderdoc_chrome_autocapture_end_source)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_electron_autocapture_api\", linux_vulkan_render_log_renderdoc_electron_autocapture_api)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_electron_autocapture_started\", linux_vulkan_render_log_renderdoc_electron_autocapture_started)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_electron_autocapture_finished\", linux_vulkan_render_log_renderdoc_electron_autocapture_finished)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_electron_autocapture_start_source\", linux_vulkan_render_log_renderdoc_electron_autocapture_start_source)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_electron_autocapture_end_source\", linux_vulkan_render_log_renderdoc_electron_autocapture_end_source)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_host_renderdoc_status\", linux_vulkan_render_log_host_renderdoc_status)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_host_chrome_status\", linux_vulkan_render_log_host_chrome_status)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_host_electron_status\", linux_vulkan_render_log_host_electron_status)")
expect(linux_compare).to_contain("linux_vulkan_render_log_compare_renderdoc_chrome_vk_enum_physical_device_count")
expect(linux_compare).to_contain("linux_vulkan_render_log_compare_renderdoc_chrome_vk_get_physical_device_properties_count")
expect(linux_compare).to_contain("linux_vulkan_render_log_compare_renderdoc_chrome_vk_get_physical_device_properties2_count")
expect(linux_compare).to_contain("linux_vulkan_render_log_compare_renderdoc_chrome_vk_get_physical_device_queue_family2_count")
expect(linux_compare).to_contain("linux_vulkan_render_log_compare_renderdoc_electron_vk_enum_physical_device_count")

step("Assert browser RenderDoc capture uses the detected tree and proven Vulkan flags")
val renderdoc_common = file_read("scripts/lib/renderdoc-evidence-common.shs")
expect(renderdoc_common).to_contain("RDOC_HOME=\"$renderdoc_home\"")
expect(renderdoc_common).to_contain("RDOC_GPU_LAUNCHER_RENDERDOC_LIB=\"$rdoc_lib\"")
expect(renderdoc_common).to_contain("--enable-features=Vulkan --use-angle=vulkan")
expect(renderdoc_common).to_contain("tools/electron-live-bitmap/renderdoc_display_html.js")
expect(renderdoc_common).to_contain("electron_display_mode=\"gpu-autocapture\"")
expect(renderdoc_common).to_contain("ELECTRON_CAPTURE_FORCE_DATA_URL=\"$electron_force_data_url\"")
expect(renderdoc_common.contains("DefaultANGLEVulkan,VulkanFromANGLE")).to_equal(false)
expect(renderdoc_common).to_contain("rdoc_best_autocapture_summary()")
expect(renderdoc_common).to_contain("summary=\"$(rdoc_best_autocapture_summary \"$log_path\")\"")
expect(renderdoc_common).to_contain("score > best_score || (score == best_score && NR >= best_line)")
expect(renderdoc_common.contains("score = NR")).to_equal(false)
val gpu_launcher = file_read("scripts/tool/renderdoc-gpu-launcher.shs")
expect(gpu_launcher).to_contain("RDOC_GPU_LAUNCHER_CLEAR_INSTANCE_LAYERS")
expect(gpu_launcher).to_contain("RDOC_GPU_LAUNCHER_CLEAR_RENDERDOC_ENABLE")
val electron_gate = file_read("scripts/check/check-renderdoc-electron-html-gate.shs")
expect(electron_gate).to_contain("tools/electron-live-bitmap/renderdoc_display_html.js")
expect(electron_gate).to_contain("pass-for-capture_html_argb")
expect(electron_gate).to_contain("[ \"$argb_required\" = \"0\" ] || [ \"$argb_status\" = \"pass\" ]")
val vulkan_only_setup = file_read("scripts/setup/build-renderdoc-linux-vulkan-only.shs")
expect(vulkan_only_setup).to_contain("RENDERDOC_LOCAL_SYSROOT")
expect(vulkan_only_setup).to_contain("local_sysroot_cmake_args()")
expect(vulkan_only_setup).to_contain("-DENABLE_GL=OFF")
expect(vulkan_only_setup).to_contain("-DENABLE_EGL=OFF")
expect(vulkan_only_setup).to_contain("-DENABLE_VULKAN=ON")

step("Assert delay-trigger shim catches ANGLE proc lookup for Vulkan")
val delay_trigger = file_read("scripts/tool/renderdoc-delay-trigger.c")
expect(delay_trigger).to_contain("void *eglGetProcAddress")
expect(delay_trigger).to_contain("rdoc_delay_trigger_eglgetproc=vkGetInstanceProcAddr")

step("Assert GPU autocapture evidence exposes frame-boundary hook counts")
expect(renderdoc_common).to_contain("rdoc_gpu_autocapture_vk_create_device_count=$(rdoc_summary_value vk_create_device \"$summary\")")
expect(renderdoc_common).to_contain("rdoc_gpu_autocapture_vk_enum_physical_device_count=$(rdoc_summary_value vk_enum_physical_device \"$summary\")")
expect(renderdoc_common).to_contain("rdoc_gpu_autocapture_vk_get_physical_device_properties_count=$(rdoc_summary_value vk_get_physical_device_properties \"$summary\")")
expect(renderdoc_common).to_contain("rdoc_gpu_autocapture_vk_get_physical_device_properties2_count=$(rdoc_summary_value vk_get_physical_device_properties2 \"$summary\")")
expect(renderdoc_common).to_contain("rdoc_gpu_autocapture_vk_get_physical_device_features2_count=$(rdoc_summary_value vk_get_physical_device_features2 \"$summary\")")
expect(renderdoc_common).to_contain("rdoc_gpu_autocapture_vk_get_physical_device_queue_family_count=$(rdoc_summary_value vk_get_physical_device_queue_family \"$summary\")")
expect(renderdoc_common).to_contain("rdoc_gpu_autocapture_vk_get_physical_device_queue_family2_count=$(rdoc_summary_value vk_get_physical_device_queue_family2 \"$summary\")")
expect(renderdoc_common).to_contain("rdoc_gpu_autocapture_vk_enum_device_extension_count=$(rdoc_summary_value vk_enum_device_extension \"$summary\")")
expect(renderdoc_common).to_contain("rdoc_gpu_autocapture_submit_count=$(rdoc_summary_value submit \"$summary\")")
expect(renderdoc_common).to_contain("rdoc_gpu_autocapture_present_count=$(rdoc_summary_value present \"$summary\")")
expect(renderdoc_common).to_contain("rdoc_gpu_autocapture_egl_swap_count=$(rdoc_summary_value egl_swap \"$summary\")")
val autocapture = file_read("scripts/tool/renderdoc-vulkan-autocapture.c")
expect(autocapture).to_contain("rdoc_autocapture_physical_device_properties2=")
expect(autocapture).to_contain("rdoc_autocapture_physical_device_properties2_pnext=")
expect(autocapture).to_contain("rdoc_autocapture_physical_device_driver_properties=")
expect(autocapture).to_contain("rdoc_autocapture_physical_device_id_properties=")
expect(autocapture).to_contain("rdoc_autocapture_instance_version=")
expect(autocapture).to_contain("\"create_instance_extension\"")
expect(autocapture).to_contain("rdoc_autocapture_egl_get_platform_display=")
expect(autocapture).to_contain("rdoc_autocapture_egl_initialize=")
expect(autocapture).to_contain("rdoc_autocapture_egl_make_current=")

step("Assert the RenderDoc guide documents lifecycle forwarding")
val guide = file_read("doc/07_guide/tooling/renderdoc_capture_infra.md")
expect(guide).to_contain("linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_api")
expect(guide).to_contain("..._started")
expect(guide).to_contain("..._finished")
expect(guide).to_contain("The shared evidence helper scores all `rdoc_autocapture_summary` rows")
expect(guide).to_contain("RDOC_GPU_LAUNCHER_CLEAR_INSTANCE_LAYERS=1")
expect(guide).to_contain("RDOC_GPU_LAUNCHER_NO_DLOPEN_FALLBACK=0")
expect(guide).to_contain("vk_get_physical_device_properties2")
expect(guide).to_contain("rdoc_autocapture_physical_device_properties2_pnext")
expect(guide).to_contain("WSI-enabled `vkCreateInstance`")
expect(guide).to_contain("rdoc_autocapture_egl_get_platform_display")
expect(guide).to_contain("chrome-vulkan-only-egl-direct-20260702")
expect(guide).to_contain("renderdoc_display_html.js")
expect(guide).to_contain("electron-vulkan-only-default-display-gpu-20260702")
```

</details>

#### chooses the most useful GPU autocapture summary from a restarted Chromium GPU log

- chooses the most useful GPU autocapture summary from a restarted Chromium GPU log
- Create a log where the useful capture summary is not the final summary
   - Expected: code equals `0`
- Read parsed metadata and confirm the useful summary wins


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chooses the most useful GPU autocapture summary from a restarted Chromium GPU log")
step("Create a log where the useful capture summary is not the final summary")
val command = "rm -rf build/test-renderdoc-autocapture-summary && mkdir -p build/test-renderdoc-autocapture-summary && cat > build/test-renderdoc-autocapture-summary/gpu.log <<'EOF'\n" +
    "rdoc_autocapture_loaded=1\n" +
    "rdoc_autocapture_summary=status:ended api:1 started:1 finished:1 start_source:delay end_source:delay submit:0 present:0 egl_swap:0 vk_create_instance:1 vk_create_device:0 vk_enum_physical_device:2 vk_enum_physical_device_return:2 vk_enum_physical_device_last_result:0 vk_enum_physical_device_last_count:3 vk_get_physical_device_properties:3 vk_get_physical_device_queue_family:0 vk_enum_device_extension:0 egl_initialize:1\n" +
    "rdoc_autocapture_loaded=1\n" +
    "rdoc_autocapture_summary=status:not-started api:0 started:0 finished:0 start_source:none end_source:none submit:0 present:0 egl_swap:0 vk_create_instance:0 vk_create_device:0 egl_initialize:0\n" +
    "EOF\n" +
    ". scripts/lib/renderdoc-evidence-common.shs && rdoc_emit_gpu_autocapture_metadata build/test-renderdoc-autocapture-summary/gpu.log > build/test-renderdoc-autocapture-summary/evidence.env"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Read parsed metadata and confirm the useful summary wins")
val evidence = file_read("build/test-renderdoc-autocapture-summary/evidence.env")
expect(evidence).to_contain("rdoc_gpu_autocapture_status=ended")
expect(evidence).to_contain("rdoc_gpu_autocapture_api=1")
expect(evidence).to_contain("rdoc_gpu_autocapture_started=1")
expect(evidence).to_contain("rdoc_gpu_autocapture_finished=1")
expect(evidence).to_contain("rdoc_gpu_autocapture_vk_create_instance_count=1")
expect(evidence).to_contain("rdoc_gpu_autocapture_vk_enum_physical_device_count=2")
expect(evidence).to_contain("rdoc_gpu_autocapture_vk_enum_physical_device_last_count=3")
expect(evidence).to_contain("rdoc_gpu_autocapture_vk_get_physical_device_properties_count=3")
```

</details>

#### normalizes blocked or internally failed Linux pass claims to aggregate failure

- normalizes blocked or internally failed Linux pass claims to aggregate failure
- Create a Linux Vulkan render-log row that passes all artifacts but still reports blocked gates
   - Expected: code equals `0`
- Read aggregate evidence and confirm blocked gates override the claimed pass
- Confirm a forged zero blocker count cannot hide a failed ARGB gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 78 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normalizes blocked or internally failed Linux pass claims to aggregate failure")
step("Create a Linux Vulkan render-log row that passes all artifacts but still reports blocked gates")
val command = "rm -rf build/test-linux-vulkan-render-log-aggregate-blocked && mkdir -p build/test-linux-vulkan-render-log-aggregate-blocked && cat > build/test-linux-vulkan-render-log-aggregate-blocked/linux.env <<'EOF'\n" +
    "linux_vulkan_render_log_compare_status=pass\n" +
    "linux_vulkan_render_log_compare_reason=pass\n" +
    "linux_vulkan_render_log_compare_blocked_gate_count=1\n" +
    "linux_vulkan_render_log_compare_blocked_gates=renderdoc-chrome-rdc\n" +
    "linux_vulkan_render_log_compare_required_api=vulkan\n" +
    "linux_vulkan_render_log_compare_pairwise_status=pass\n" +
    "linux_vulkan_render_log_compare_simple_vulkan_gate_status=pass\n" +
    "linux_vulkan_render_log_compare_browser_backing_gate_status=pass\n" +
    "linux_vulkan_render_log_compare_pairwise_gate_status=pass\n" +
    "linux_vulkan_render_log_compare_argb_source_gate_status=pass\n" +
    "linux_vulkan_render_log_compare_renderdoc_gate_status=pass\n" +
    "linux_vulkan_render_log_compare_renderdoc_simple_status=pass\n" +
    "linux_vulkan_render_log_compare_renderdoc_simple_env_file_status=pass\n" +
    "linux_vulkan_render_log_compare_renderdoc_simple_artifact_file_status=pass\n" +
    "linux_vulkan_render_log_compare_renderdoc_simple_artifact_magic=RDOC\n" +
    "linux_vulkan_render_log_compare_renderdoc_chrome_status=pass\n" +
    "linux_vulkan_render_log_compare_renderdoc_chrome_env_file_status=pass\n" +
    "linux_vulkan_render_log_compare_renderdoc_chrome_artifact_file_status=pass\n" +
    "linux_vulkan_render_log_compare_renderdoc_chrome_artifact_magic=RDOC\n" +
    "linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_api=1\n" +
    "linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_started=1\n" +
    "linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_finished=1\n" +
    "linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_start_source=delay\n" +
    "linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_end_source=delay\n" +
    "linux_vulkan_render_log_compare_renderdoc_electron_status=pass\n" +
    "linux_vulkan_render_log_compare_renderdoc_electron_env_file_status=pass\n" +
    "linux_vulkan_render_log_compare_renderdoc_electron_artifact_file_status=pass\n" +
    "linux_vulkan_render_log_compare_renderdoc_electron_artifact_magic=RDOC\n" +
    "linux_vulkan_render_log_compare_renderdoc_electron_autocapture_api=1\n" +
    "linux_vulkan_render_log_compare_renderdoc_electron_autocapture_started=1\n" +
    "linux_vulkan_render_log_compare_renderdoc_electron_autocapture_finished=1\n" +
    "linux_vulkan_render_log_compare_renderdoc_electron_autocapture_start_source=delay\n" +
    "linux_vulkan_render_log_compare_renderdoc_electron_autocapture_end_source=delay\n" +
    "linux_vulkan_render_log_compare_host_renderdoc_status=pass\n" +
    "linux_vulkan_render_log_compare_host_renderdoc_tool=renderdoccmd\n" +
    "linux_vulkan_render_log_compare_host_chrome_status=pass\n" +
    "linux_vulkan_render_log_compare_host_chrome_tool=google-chrome\n" +
    "linux_vulkan_render_log_compare_host_electron_status=pass\n" +
    "linux_vulkan_render_log_compare_host_electron_tool=electron\n" +
    "EOF\n" +
    "BUILD_DIR=build/test-linux-vulkan-render-log-aggregate-blocked/out REPORT_PATH=build/test-linux-vulkan-render-log-aggregate-blocked/report.md LINUX_VULKAN_RENDER_LOG_COMPARE_ENV=build/test-linux-vulkan-render-log-aggregate-blocked/linux.env sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs >/dev/null && " +
    "sed -e 's/blocked_gate_count=1/blocked_gate_count=0/' -e 's/blocked_gates=renderdoc-chrome-rdc/blocked_gates=none/' -e 's/argb_source_gate_status=pass/argb_source_gate_status=fail/' build/test-linux-vulkan-render-log-aggregate-blocked/linux.env > build/test-linux-vulkan-render-log-aggregate-blocked/forged.env && " +
    "BUILD_DIR=build/test-linux-vulkan-render-log-aggregate-blocked/forged-out REPORT_PATH=build/test-linux-vulkan-render-log-aggregate-blocked/forged-report.md LINUX_VULKAN_RENDER_LOG_COMPARE_ENV=build/test-linux-vulkan-render-log-aggregate-blocked/forged.env sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs >/dev/null"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Read aggregate evidence and confirm blocked gates override the claimed pass")
val evidence = file_read("build/test-linux-vulkan-render-log-aggregate-blocked/out/evidence.env")
expect(evidence).to_contain("linux_vulkan_render_log_compare_status=fail")
expect(evidence).to_contain("linux_vulkan_render_log_compare_reason=linux-vulkan-blocked-gates-present:1")
expect(evidence).to_contain("linux_vulkan_render_log_compare_blocked_gate_count=1")
expect(evidence).to_contain("linux_vulkan_render_log_compare_blocked_gates=renderdoc-chrome-rdc")
expect(evidence).to_contain("linux_vulkan_render_log_compare_simple_vulkan_gate_status=pass")
expect(evidence).to_contain("linux_vulkan_render_log_compare_browser_backing_gate_status=pass")
expect(evidence).to_contain("linux_vulkan_render_log_compare_pairwise_gate_status=pass")
expect(evidence).to_contain("linux_vulkan_render_log_compare_argb_source_gate_status=pass")
expect(evidence).to_contain("linux_vulkan_render_log_compare_renderdoc_gate_status=pass")
expect(evidence).to_contain("linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_api=1")
expect(evidence).to_contain("linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_started=1")
expect(evidence).to_contain("linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_finished=1")
expect(evidence).to_contain("linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_start_source=delay")
expect(evidence).to_contain("linux_vulkan_render_log_compare_renderdoc_chrome_autocapture_end_source=delay")
expect(evidence).to_contain("linux_vulkan_render_log_compare_renderdoc_electron_autocapture_api=1")
expect(evidence).to_contain("linux_vulkan_render_log_compare_renderdoc_electron_autocapture_started=1")
expect(evidence).to_contain("linux_vulkan_render_log_compare_renderdoc_electron_autocapture_finished=1")
expect(evidence).to_contain("linux_vulkan_render_log_compare_renderdoc_electron_autocapture_start_source=delay")
expect(evidence).to_contain("linux_vulkan_render_log_compare_renderdoc_electron_autocapture_end_source=delay")

step("Confirm a forged zero blocker count cannot hide a failed ARGB gate")
val forged = file_read("build/test-linux-vulkan-render-log-aggregate-blocked/forged-out/evidence.env")
expect(forged).to_contain("linux_vulkan_render_log_compare_status=fail")
expect(forged).to_contain("linux_vulkan_render_log_compare_reason=linux-vulkan-argb-source-gate-not-pass:fail")
expect(forged).to_contain("linux_vulkan_render_log_compare_blocked_gate_count=0")
expect(forged).to_contain("linux_vulkan_render_log_compare_argb_source_gate_status=fail")
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

- **Plan:** `doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md`
- **Design:** `doc/07_guide/tooling/renderdoc_capture_infra.md`
- **Research:** `doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `35d4ac12298af570ac3dfd9dbfc76d38d4dabe3f8ce5e3635131cc2d13b8646f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `35d4ac12298af570ac3dfd9dbfc76d38d4dabe3f8ce5e3635131cc2d13b8646f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `35d4ac12298af570ac3dfd9dbfc76d38d4dabe3f8ce5e3635131cc2d13b8646f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/03_system/check/linux_vulkan_render_log_aggregate_forwarding_spec.spl
mirror: doc/06_spec/03_system/check/linux_vulkan_render_log_aggregate_forwarding_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/linux_vulkan_render_log_aggregate_forwarding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/linux_vulkan_render_log_aggregate_forwarding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/linux_vulkan_render_log_aggregate_forwarding_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
