# Linux Vulkan Render Log Aggregate Forwarding

> Verifies the lightweight contract that Linux Vulkan render-log diagnostics keep their structured blocker and per-gate fields visible at aggregate level. This spec reads wrapper source directly so it can run without a Linux GUI host, RenderDoc, Chrome, Electron, Vulkan, or the broad GUI aggregate fixture.

<!-- sdn-diagram:id=linux_vulkan_render_log_aggregate_forwarding_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linux_vulkan_render_log_aggregate_forwarding_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linux_vulkan_render_log_aggregate_forwarding_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linux_vulkan_render_log_aggregate_forwarding_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

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
| Updated | 2026-06-01 |
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

- Read the Linux Vulkan comparison wrapper
- Assert the Linux wrapper emits blocked gates and per-gate statuses
- Read the GUI RenderDoc aggregate wrapper
- Assert the aggregate reads the Linux structured blocker fields
- Assert blocked Linux rows cannot pass aggregate validation
- Assert the aggregate emits the Linux structured gate fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the Linux Vulkan comparison wrapper")
val linux_compare = file_read("scripts/check/check-linux-vulkan-render-log-compare.shs")

step("Assert the Linux wrapper emits blocked gates and per-gate statuses")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_blocked_gate_count\" \"$blocked_gate_count\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_blocked_gates\" \"$blocked_gates\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_simple_vulkan_gate_status\" \"$simple_vulkan_gate_status\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_browser_backing_gate_status\" \"$browser_backing_gate_status\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_pairwise_gate_status\" \"$pixel_gate_status\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_argb_source_gate_status\" \"$argb_source_gate_status\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_renderdoc_gate_status\" \"$renderdoc_gate_status\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_renderdoc_simple_artifact_file_status\" \"$simple_artifact_file_status\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_renderdoc_chrome_artifact_file_status\" \"$chrome_artifact_file_status\"")
expect(linux_compare).to_contain("render_log_append_kv \"linux_vulkan_render_log_compare_renderdoc_electron_artifact_file_status\" \"$electron_artifact_file_status\"")
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
expect(aggregate).to_contain("linux_vulkan_render_log_host_renderdoc_status = value_of(\"linux_vulkan_render_log_compare_host_renderdoc_status\"")
expect(aggregate).to_contain("linux_vulkan_render_log_host_chrome_status = value_of(\"linux_vulkan_render_log_compare_host_chrome_status\"")
expect(aggregate).to_contain("linux_vulkan_render_log_host_electron_status = value_of(\"linux_vulkan_render_log_compare_host_electron_status\"")

step("Assert blocked Linux rows cannot pass aggregate validation")
expect(aggregate).to_contain("elif linux_vulkan_render_log_blocked_gate_count != \"0\":")
expect(aggregate).to_contain("linux_vulkan_render_log_reason = \"linux-vulkan-blocked-gates-present:\"")

step("Assert the aggregate emits the Linux structured gate fields")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_blocked_gate_count\", linux_vulkan_render_log_blocked_gate_count)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_blocked_gates\", linux_vulkan_render_log_blocked_gates)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_simple_vulkan_gate_status\", linux_vulkan_render_log_simple_vulkan_gate_status)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_browser_backing_gate_status\", linux_vulkan_render_log_browser_backing_gate_status)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_pairwise_gate_status\", linux_vulkan_render_log_pairwise_gate_status)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_argb_source_gate_status\", linux_vulkan_render_log_argb_source_gate_status)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_gate_status\", linux_vulkan_render_log_renderdoc_gate_status)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_host_renderdoc_status\", linux_vulkan_render_log_host_renderdoc_status)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_host_chrome_status\", linux_vulkan_render_log_host_chrome_status)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_host_electron_status\", linux_vulkan_render_log_host_electron_status)")
```

</details>

#### normalizes a claimed Linux pass with blocked gates to aggregate failure

- Create a Linux Vulkan render-log row that passes all artifacts but still reports blocked gates
   - Expected: code equals `0`
- Read aggregate evidence and confirm blocked gates override the claimed pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
    "linux_vulkan_render_log_compare_renderdoc_electron_status=pass\n" +
    "linux_vulkan_render_log_compare_renderdoc_electron_env_file_status=pass\n" +
    "linux_vulkan_render_log_compare_renderdoc_electron_artifact_file_status=pass\n" +
    "linux_vulkan_render_log_compare_renderdoc_electron_artifact_magic=RDOC\n" +
    "linux_vulkan_render_log_compare_host_renderdoc_status=pass\n" +
    "linux_vulkan_render_log_compare_host_renderdoc_tool=renderdoccmd\n" +
    "linux_vulkan_render_log_compare_host_chrome_status=pass\n" +
    "linux_vulkan_render_log_compare_host_chrome_tool=google-chrome\n" +
    "linux_vulkan_render_log_compare_host_electron_status=pass\n" +
    "linux_vulkan_render_log_compare_host_electron_tool=electron\n" +
    "EOF\n" +
    "BUILD_DIR=build/test-linux-vulkan-render-log-aggregate-blocked/out REPORT_PATH=build/test-linux-vulkan-render-log-aggregate-blocked/report.md LINUX_VULKAN_RENDER_LOG_COMPARE_ENV=build/test-linux-vulkan-render-log-aggregate-blocked/linux.env sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs >/dev/null"
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

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md](doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md)


</details>
