# Linux Vulkan RenderDoc Reason Forwarding

> Verifies the lightweight contract that Linux Vulkan render-log diagnostics keep the actionable Chrome/Electron RenderDoc failure reason visible at aggregate level. This spec intentionally avoids the broad GUI aggregate fixture so it can run quickly when the full aggregate SSpec is too expensive for a focused check.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linux Vulkan RenderDoc Reason Forwarding

Verifies the lightweight contract that Linux Vulkan render-log diagnostics keep the actionable Chrome/Electron RenderDoc failure reason visible at aggregate level. This spec intentionally avoids the broad GUI aggregate fixture so it can run quickly when the full aggregate SSpec is too expensive for a focused check.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md |
| Source | `test/03_system/check/linux_vulkan_renderdoc_reason_forwarding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the lightweight contract that Linux Vulkan render-log diagnostics keep
the actionable Chrome/Electron RenderDoc failure reason visible at aggregate
level. This spec intentionally avoids the broad GUI aggregate fixture so it can
run quickly when the full aggregate SSpec is too expensive for a focused check.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/linux_vulkan_renderdoc_reason_forwarding_spec.spl --mode=interpreter --clean
```

## Acceptance

- The Linux comparison wrapper prefers
  `rdoc_external_host_capture_reason_raw` before the generic gate reason.
- The aggregate status wrapper reads and emits Simple, Chrome, and Electron
  Linux RenderDoc reason keys.
- The aggregate status wrapper also reads and emits
  `linux_vulkan_render_log_compare_blocked_gate_count` and
  `linux_vulkan_render_log_compare_blocked_gates`, so a top-level report can
  identify whether Linux is blocked on Chrome RDOC, Electron RDOC, browser
  backing, ARGB source evidence, or another native-render-log gate.
- The current hardening report records zero Linux RenderDoc blockers and RDOC
  magic for Simple, Chrome, and Electron capture artifacts.

## Why This Exists

The full GUI RenderDoc aggregate is intentionally broad: it combines Simple
Engine2D Vulkan evidence, browser backing, ARGB pixel comparison, RenderDoc
capture files, platform portability, 4K showcase, and 8K showcase evidence.
When that aggregate is incomplete, a single reason such as
`renderdoc-chrome-fail;renderdoc-electron-fail` is not enough for an operator
or a parallel agent to know what to fix next.

The Linux render-log compare wrapper already computes a blocked-gate count and
comma-separated blocked gate list. The aggregate must preserve those fields
instead of only preserving the summarized reason. Otherwise the top-level
evidence can say "Linux render log compare failed" while hiding whether the
failure is an expected missing browser `.rdc`, a pixel mismatch, a missing
Vulkan browser backing proof, or a missing Simple RenderDoc artifact.

## Debugging

Run the direct Linux wrapper first when working only on this lane:

```sh
BUILD_DIR=build/linux-vulkan-render-log-compare \
  sh scripts/check/check-linux-vulkan-render-log-compare.shs
```

Then run the aggregate with output suppressed and inspect the forwarded keys:

```sh
BUILD_DIR=build/gui-renderdoc-feature-coverage-status \
REPORT_PATH=build/gui-renderdoc-feature-coverage-status/report.md \
GUI_RENDERDOC_AGGREGATE_PRINT_ENV=0 \
  sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

The aggregate output must include:

- `linux_vulkan_render_log_compare_blocked_gate_count`
- `linux_vulkan_render_log_compare_blocked_gates`
- `linux_vulkan_render_log_compare_renderdoc_chrome_reason`
- `linux_vulkan_render_log_compare_renderdoc_electron_reason`

Historical Linux hosts can have passing Simple RenderDoc evidence while Chrome
and Electron browser `.rdc` evidence remains missing or crashed under RenderDoc.
That incomplete state is actionable only when the blocked gate list is visible
at aggregate level.

## Completion Criteria

This spec does not prove that Linux Vulkan RenderDoc capture is complete. It
only proves the aggregate keeps enough diagnostic information for a later host
run to be judged correctly. Goal completion still requires:

- `linux_vulkan_render_log_compare_status=pass`
- `linux_vulkan_render_log_compare_blocked_gate_count=0`
- `linux_vulkan_render_log_compare_renderdoc_simple_artifact_magic=RDOC`
- `linux_vulkan_render_log_compare_renderdoc_chrome_artifact_magic=RDOC`
- `linux_vulkan_render_log_compare_renderdoc_electron_artifact_magic=RDOC`
- `gui_showcase_4k_200fps_status=pass`
- `gui_showcase_8k_perf_status=pass`

If Chrome or Electron browser capture fails under RenderDoc, keep the aggregate
status incomplete and use the forwarded blocked gates to decide the next action.
Do not replace missing `.rdc` proof with ARGB bitmap proof, browser backing
metadata, or cached log text. When all three artifacts have `RDOC` magic in the
current hardening report, keep the blocker record superseded by that aggregate.

## Failure Interpretation

`renderdoc-chrome-rdc` means the original Chrome/Chromium browser RenderDoc
artifact is not a verified regular RDOC file. `renderdoc-electron-rdc` means the
Electron Chromium RenderDoc artifact is not a verified regular RDOC file. Both
can coexist with passing pairwise ARGB comparison and passing browser backing;
that combination proves browser-rendered pixels and Vulkan backing, but it does
not prove native GPU debugger capture.

When the aggregate prints both browser blocked gates, the next platform action
is to rerun Chrome and Electron on a prepared Linux GUI host with RenderDoc
child-hook diagnostics, then replace the stale evidence only if the new capture
files have `RDOC` magic. If a capture still fails, preserve the concrete reason
such as `chromium-gpu-process-crashed-under-renderdoc` or `missing-rdc`.

## Scenarios

### Linux Vulkan RenderDoc reason forwarding

#### keeps actionable browser RenderDoc failure reasons in the Linux comparison and aggregate

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps actionable browser RenderDoc failure reasons in the Linux comparison and aggregate
- Read the Linux comparison wrapper
- Assert Chrome raw capture reason is preferred before generic fallbacks
- Read the GUI RenderDoc aggregate wrapper
- Assert aggregate reads and emits per-backend Linux RenderDoc reasons and blocked gates


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps actionable browser RenderDoc failure reasons in the Linux comparison and aggregate")
step("Read the Linux comparison wrapper")
val linux_compare = file_read("scripts/check/check-linux-vulkan-render-log-compare.shs")

step("Assert Chrome raw capture reason is preferred before generic fallbacks")
expect(linux_compare).to_contain("chrome_rdoc_reason=\"$(render_log_value_of rdoc_external_host_capture_reason_raw \"$RDOC_HTML_EVIDENCE_ENV\")\"")
expect(linux_compare).to_contain("chrome_rdoc_reason=\"$(render_log_value_of rdoc_capture_reason \"$RDOC_HTML_EVIDENCE_ENV\")\"")
expect(linux_compare).to_contain("render_log_reason_from_rdoc_env \"$RDOC_HTML_EVIDENCE_ENV\" rdoc_external_host_gate_reason rdoc_external_host_capture_reason_raw")

step("Read the GUI RenderDoc aggregate wrapper")
val aggregate = file_read("scripts/check/check-gui-renderdoc-feature-coverage-status.shs")

step("Assert aggregate reads and emits per-backend Linux RenderDoc reasons and blocked gates")
expect(aggregate).to_contain("linux_vulkan_render_log_blocked_gate_count = value_of(\"linux_vulkan_render_log_compare_blocked_gate_count\"")
expect(aggregate).to_contain("linux_vulkan_render_log_blocked_gates = value_of(\"linux_vulkan_render_log_compare_blocked_gates\"")
expect(aggregate).to_contain("linux_vulkan_render_log_renderdoc_simple_reason = value_of(\"linux_vulkan_render_log_compare_renderdoc_simple_reason\"")
expect(aggregate).to_contain("linux_vulkan_render_log_renderdoc_chrome_reason = value_of(\"linux_vulkan_render_log_compare_renderdoc_chrome_reason\"")
expect(aggregate).to_contain("linux_vulkan_render_log_renderdoc_electron_reason = value_of(\"linux_vulkan_render_log_compare_renderdoc_electron_reason\"")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_blocked_gate_count\", linux_vulkan_render_log_blocked_gate_count)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_blocked_gates\", linux_vulkan_render_log_blocked_gates)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_simple_reason\", linux_vulkan_render_log_renderdoc_simple_reason)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_chrome_reason\", linux_vulkan_render_log_renderdoc_chrome_reason)")
expect(aggregate).to_contain("emit(\"linux_vulkan_render_log_compare_renderdoc_electron_reason\", linux_vulkan_render_log_renderdoc_electron_reason)")
```

</details>

#### records the current Linux RenderDoc aggregate as unblocked with RDOC artifacts

- records the current Linux RenderDoc aggregate as unblocked with RDOC artifacts
- Read the current Linux RenderDoc hardening report
- Assert the current aggregate reports a passing RenderDoc gate
- Assert all three RenderDoc artifacts are verified as RDOC captures


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records the current Linux RenderDoc aggregate as unblocked with RDOC artifacts")
step("Read the current Linux RenderDoc hardening report")
val report = file_read("doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md")

step("Assert the current aggregate reports a passing RenderDoc gate")
expect(report).to_contain("- status: pass")
expect(report).to_contain("- blocked_gate_count: 0")
expect(report).to_contain("- renderdoc_gate_status: pass")

step("Assert all three RenderDoc artifacts are verified as RDOC captures")
expect(report).to_contain("- simple_rdoc_artifact_magic: RDOC")
expect(report).to_contain("- chrome_rdoc_artifact_magic: RDOC")
expect(report).to_contain("- electron_rdoc_artifact_magic: RDOC")
expect(report).to_contain("build/renderdoc/canonical-probe/simple/simple_gui_app_capture.rdc")
expect(report).to_contain("build/renderdoc/chrome-implicit-layer-default-autocapture/html/gpu_chrome_capture.rdc")
expect(report).to_contain("build/renderdoc/electron-implicit-layer-default-autocapture/electron-html/electron_gpu_capture.rdc")
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

- Canonical SPipe generation for source `d34f3f44e9f5b800eb71d3313a7598c599e9b28c7bfce3ccc98452fc118b62f0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d34f3f44e9f5b800eb71d3313a7598c599e9b28c7bfce3ccc98452fc118b62f0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d34f3f44e9f5b800eb71d3313a7598c599e9b28c7bfce3ccc98452fc118b62f0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/03_system/check/linux_vulkan_renderdoc_reason_forwarding_spec.spl
mirror: doc/06_spec/03_system/check/linux_vulkan_renderdoc_reason_forwarding_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/linux_vulkan_renderdoc_reason_forwarding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/linux_vulkan_renderdoc_reason_forwarding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/linux_vulkan_renderdoc_reason_forwarding_spec.spl:157:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records the current Linux RenderDoc aggregate as unblocked with RDOC artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
