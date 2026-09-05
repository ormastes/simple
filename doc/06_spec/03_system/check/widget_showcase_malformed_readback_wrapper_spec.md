# Widget Showcase Malformed Readback Wrapper Contract

> Validates that the retained GUI showcase performance wrapper handles malformed probe readback rows through normal status evidence instead of raw shell numeric test errors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Showcase Malformed Readback Wrapper Contract

Validates that the retained GUI showcase performance wrapper handles malformed probe readback rows through normal status evidence instead of raw shell numeric test errors.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/widget_showcase_malformed_readback_wrapper_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that the retained GUI showcase performance wrapper handles malformed
probe readback rows through normal status evidence instead of raw shell numeric
test errors.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
bin/simple test test/03_system/check/widget_showcase_malformed_readback_wrapper_spec.spl --mode=interpreter
```

## Operator Flow

1. Run this spec after changing `scripts/check/check-widget-showcase-4k-200fps.shs`.
2. Inspect `build/test-widget-showcase-malformed-readback-4k/status.env` for
   the 4K producer result.
3. Inspect `build/test-widget-showcase-malformed-readback-8k/status.env` for
   the 8K producer result.
4. Treat any shell `integer expression expected` diagnostic as a regression in
   malformed readback handling.

## Acceptance

- A malformed 4K `nonzero_pixels` row fails with
  `reason=readback-nonblank-unverified`.
- A malformed 8K `nonzero_pixels` row fails with
  `reason=readback-nonblank-unverified`.
- Malformed checksum, render mode, and redraw rows fail with their specific
  producer-side reasons for both 4K and 8K.
- Both rows emit `*_nonzero_pixels_status=fail`.
- The wrapper exits through its normal failure path without shell integer-test
  diagnostics.

## Test Strategy

The spec uses a fake `simple` executable that accepts the wrapper's
`native-build` command and copies a fake native probe script to the requested
`--output` path. The fake native probe emits valid geometry and checksum rows
but malformed `nonzero_pixels=not-a-number` and `redraw_frames=bad` values.
This covers the wrapper producer logic without launching a GUI host or a real
native compiler.

## Failure Semantics

Malformed producer values are not completion evidence. They must become typed
status rows in `status.env` so the aggregate can fail closed with a useful
reason and future agents can debug the exact bad field.

## Evidence Keys

The 4K malformed readback case must emit:

- `gui_showcase_4k_200fps_status=fail`
- `gui_showcase_4k_200fps_reason=readback-nonblank-unverified`
- `gui_showcase_4k_200fps_width=3840`
- `gui_showcase_4k_200fps_height=2160`
- `gui_showcase_4k_200fps_pixels=8294400`
- `gui_showcase_4k_200fps_nonzero_pixels=not-a-number`
- `gui_showcase_4k_200fps_nonzero_pixels_status=fail`
- `gui_showcase_4k_200fps_checksum=123456`
- `gui_showcase_4k_200fps_checksum_status=pass`
- `gui_showcase_4k_200fps_render_mode=retained-static-frame`
- `gui_showcase_4k_200fps_retained_render_mode_status=pass`
- `gui_showcase_4k_200fps_redraw_frames=bad`
- `gui_showcase_4k_200fps_retained_redraw_status=fail`

The 8K malformed readback case must emit the matching
`gui_showcase_8k_perf_*` keys with:

- `gui_showcase_8k_perf_width=7680`
- `gui_showcase_8k_perf_height=4320`
- `gui_showcase_8k_perf_pixels=33177600`
- `gui_showcase_8k_perf_nonzero_pixels=not-a-number`
- `gui_showcase_8k_perf_nonzero_pixels_status=fail`
- `gui_showcase_8k_perf_redraw_frames=bad`
- `gui_showcase_8k_perf_retained_redraw_status=fail`

## Troubleshooting

If this spec fails before creating `status.env`, inspect the fake `simple`
script and fake native probe under the matching `build/test-widget-showcase-*`
directory. If it fails with `integer expression expected` in stderr, the
wrapper reintroduced a raw shell numeric comparison against untrusted probe
text. If it emits `pass`, malformed readback rows are being accepted as
completion evidence and the wrapper must fail closed before aggregate testing.

## Relation To Aggregate Gates

The aggregate has separate fail-closed checks for malformed nonzero-pixel,
checksum, retained-mode, RSS, and source-revision evidence. This wrapper spec
keeps the producer side aligned so malformed native probe output is classified
at the source, before it is consumed by
`check-gui-renderdoc-feature-coverage-status.shs`.

## Non-goals

This spec does not exercise real native compilation, frame timing, RSS budget
measurement, GPU readback, RenderDoc capture, or browser/Electron parity. The
fake native probe intentionally isolates malformed text handling in the wrapper
itself.

## Completion Boundary

This spec covers wrapper robustness for malformed retained readback rows only.
It does not prove real 4K/8K throughput, native compiler performance, Vulkan or
Metal backend selection, or RenderDoc capture validity.

## Scenarios

### Widget showcase malformed readback wrapper contract

#### fails malformed 4K readback rows without shell integer diagnostics

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fails malformed 4K readback rows without shell integer diagnostics
- Run the wrapper with a fake native 4K probe
   - Expected: code equals `1`
   - Expected: stderr does not contain `integer expression expected`
- Assert the wrapper writes a typed malformed-readback status
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_reason") equals `readback-nonblank-unverified`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_nonzero_pixels_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_retained_redraw_status") equals `fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails malformed 4K readback rows without shell integer diagnostics")
step("Run the wrapper with a fake native 4K probe")
val command = _fake_probe_command("build/test-widget-showcase-malformed-readback-4k", "4k")
val (_stdout, stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)
expect(stderr.contains("integer expression expected")).to_equal(false)

step("Assert the wrapper writes a typed malformed-readback status")
val evidence = file_read("build/test-widget-showcase-malformed-readback-4k/status.env")
expect(_value_of(evidence, "gui_showcase_4k_200fps_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_4k_200fps_reason")).to_equal("readback-nonblank-unverified")
expect(_value_of(evidence, "gui_showcase_4k_200fps_nonzero_pixels_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_4k_200fps_retained_redraw_status")).to_equal("fail")
```

</details>

#### fails malformed 8K readback rows without shell integer diagnostics

- fails malformed 8K readback rows without shell integer diagnostics
- Run the wrapper with a fake native 8K probe
   - Expected: code equals `1`
   - Expected: stderr does not contain `integer expression expected`
- Assert the wrapper writes a typed malformed-readback status
   - Expected: _value_of(evidence, "gui_showcase_8k_perf_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_8k_perf_reason") equals `readback-nonblank-unverified`
   - Expected: _value_of(evidence, "gui_showcase_8k_perf_nonzero_pixels_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_8k_perf_retained_redraw_status") equals `fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails malformed 8K readback rows without shell integer diagnostics")
step("Run the wrapper with a fake native 8K probe")
val command = _fake_probe_command("build/test-widget-showcase-malformed-readback-8k", "8k")
val (_stdout, stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)
expect(stderr.contains("integer expression expected")).to_equal(false)

step("Assert the wrapper writes a typed malformed-readback status")
val evidence = file_read("build/test-widget-showcase-malformed-readback-8k/status.env")
expect(_value_of(evidence, "gui_showcase_8k_perf_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_8k_perf_reason")).to_equal("readback-nonblank-unverified")
expect(_value_of(evidence, "gui_showcase_8k_perf_nonzero_pixels_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_8k_perf_retained_redraw_status")).to_equal("fail")
```

</details>

#### classifies malformed 4K checksum rows without shell integer diagnostics

- classifies malformed 4K checksum rows without shell integer diagnostics
- Run the wrapper with a fake native 4K checksum failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies malformed 4K checksum rows without shell integer diagnostics")
step("Run the wrapper with a fake native 4K checksum failure")
_assert_malformed_case("build/test-widget-showcase-malformed-checksum-4k", "4k", "gui_showcase_4k_200fps", "100", "bad-checksum", "retained-static-frame", "1", "readback-checksum-missing", "checksum_status")
```

</details>

#### classifies malformed 8K checksum rows without shell integer diagnostics

- classifies malformed 8K checksum rows without shell integer diagnostics
- Run the wrapper with a fake native 8K checksum failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies malformed 8K checksum rows without shell integer diagnostics")
step("Run the wrapper with a fake native 8K checksum failure")
_assert_malformed_case("build/test-widget-showcase-malformed-checksum-8k", "8k", "gui_showcase_8k_perf", "100", "bad-checksum", "retained-static-frame", "1", "readback-checksum-missing", "checksum_status")
```

</details>

#### classifies malformed 4K render mode rows without shell integer diagnostics

- classifies malformed 4K render mode rows without shell integer diagnostics
- Run the wrapper with a fake native 4K render mode failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies malformed 4K render mode rows without shell integer diagnostics")
step("Run the wrapper with a fake native 4K render mode failure")
_assert_malformed_case("build/test-widget-showcase-malformed-render-mode-4k", "4k", "gui_showcase_4k_200fps", "100", "123456", "redraw-every-frame", "1", "not-retained-static-frame", "retained_render_mode_status")
```

</details>

#### classifies malformed 8K render mode rows without shell integer diagnostics

- classifies malformed 8K render mode rows without shell integer diagnostics
- Run the wrapper with a fake native 8K render mode failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies malformed 8K render mode rows without shell integer diagnostics")
step("Run the wrapper with a fake native 8K render mode failure")
_assert_malformed_case("build/test-widget-showcase-malformed-render-mode-8k", "8k", "gui_showcase_8k_perf", "100", "123456", "redraw-every-frame", "1", "not-retained-static-frame", "retained_render_mode_status")
```

</details>

#### classifies malformed 4K redraw rows without shell integer diagnostics

- classifies malformed 4K redraw rows without shell integer diagnostics
- Run the wrapper with a fake native 4K redraw failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies malformed 4K redraw rows without shell integer diagnostics")
step("Run the wrapper with a fake native 4K redraw failure")
_assert_malformed_case("build/test-widget-showcase-malformed-redraw-4k", "4k", "gui_showcase_4k_200fps", "100", "123456", "retained-static-frame", "bad", "unexpected-redraw-count", "retained_redraw_status")
```

</details>

#### classifies malformed 8K redraw rows without shell integer diagnostics

- classifies malformed 8K redraw rows without shell integer diagnostics
- Run the wrapper with a fake native 8K redraw failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies malformed 8K redraw rows without shell integer diagnostics")
step("Run the wrapper with a fake native 8K redraw failure")
_assert_malformed_case("build/test-widget-showcase-malformed-redraw-8k", "8k", "gui_showcase_8k_perf", "100", "123456", "retained-static-frame", "bad", "unexpected-redraw-count", "retained_redraw_status")
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

- **Plan:** `doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md`
- **Design:** `doc/07_guide/tooling/renderdoc_capture_infra.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ae4a4e970fe5c942320dd683bb4c9e424b08c0bfcd3d3a0d562ddce10396b763`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ae4a4e970fe5c942320dd683bb4c9e424b08c0bfcd3d3a0d562ddce10396b763`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ae4a4e970fe5c942320dd683bb4c9e424b08c0bfcd3d3a0d562ddce10396b763`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/check/widget_showcase_malformed_readback_wrapper_spec.spl
mirror: doc/06_spec/03_system/check/widget_showcase_malformed_readback_wrapper_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/widget_showcase_malformed_readback_wrapper_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/widget_showcase_malformed_readback_wrapper_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/widget_showcase_malformed_readback_wrapper_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/widget_showcase_malformed_readback_wrapper_spec.spl:161:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails malformed 4K readback rows without shell integer diagnostics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/widget_showcase_malformed_readback_wrapper_spec.spl:177:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails malformed 8K readback rows without shell integer diagnostics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/widget_showcase_malformed_readback_wrapper_spec.spl:193:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies malformed 4K checksum rows without shell integer diagnostics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
