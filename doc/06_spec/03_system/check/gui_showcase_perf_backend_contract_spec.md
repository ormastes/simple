# GUI Showcase Perf Backend Contract

> Validates that retained 4K and 8K GUI showcase performance evidence must come from the canonical retained widget showcase backend. A producer cannot satisfy completion by reporting a generic or unrelated backend label.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Showcase Perf Backend Contract

Validates that retained 4K and 8K GUI showcase performance evidence must come from the canonical retained widget showcase backend. A producer cannot satisfy completion by reporting a generic or unrelated backend label.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_showcase_perf_backend_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that retained 4K and 8K GUI showcase performance evidence must come
from the canonical retained widget showcase backend. A producer cannot satisfy
completion by reporting a generic or unrelated backend label.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Acceptance

- A retained 4K row with `backend=wrong-backend` is normalized to `fail`.
- A retained 8K row with `backend=wrong-backend` is normalized to `fail`.
- The failure reasons are `invalid-4k-backend:wrong-backend` and
  `invalid-8k-backend:wrong-backend`.
- Otherwise valid retained 4K and 8K rows with stale failure reasons are
  normalized back to canonical success reasons.
- All surrounding timing, RSS, checksum, retained-mode, source, native, and
  fallback fields remain valid so the backend classifier is the first failing
  gate.

## Syntax

```sh
SIMPLE_LIB=src bin/simple test --no-session-daemon \
  test/03_system/check/gui_showcase_perf_backend_contract_spec.spl \
  --mode=interpreter --clean --fail-fast
```

## Evidence Contract

This spec does not render a real 4K or 8K GUI frame. It creates controlled
retained-performance evidence rows and sends them through the same aggregate
normalizer used by the top-level GUI/Web/2D completion criteria. The fixture
keeps timing, RSS, checksum, retained render mode, source revision metadata,
self-hosted release Simple provenance, native binary metadata, alias source
metadata, build logs, runtime logs, and fallback state valid. That lets the
scenario prove the exact backend and success-reason behavior without depending
on a live GUI/GPU host.

The aggregate must reject an otherwise valid retained row when the backend is
not `simple-retained-widget-showcase`. This prevents unrelated benchmark rows,
browser rows, CPU-only rows, or external renderer rows from satisfying the
retained 200 FPS showcase gate.

The aggregate must also normalize stale failure reasons after all retained
proof gates pass. A stale `missing-required-...` reason paired with
`status=pass` is contradictory evidence and cannot be accepted by the top-level
completion gate. Valid 4K rows must emit `met-200fps`; valid 8K rows must emit
`met-target-fps`.

## Test Matrix

1. 4K retained fixture with `backend=wrong-backend`.
2. 8K retained fixture with `backend=wrong-backend`.
3. 4K retained fixture with valid backend and stale missing-evidence reason.
4. 8K retained fixture with valid backend and stale missing-evidence reason.

## Required Output Rows

Reviewers should inspect these normalized rows before accepting the retained
perf aggregate behavior:

- `gui_showcase_4k_200fps_status`
- `gui_showcase_4k_200fps_reason`
- `gui_showcase_4k_200fps_backend`
- `gui_showcase_4k_200fps_alias_raw_rt_count`
- `gui_showcase_4k_200fps_simple_bin_source`
- `gui_showcase_4k_200fps_native_build_mode`
- `gui_showcase_4k_200fps_fallback_state`
- `gui_showcase_8k_perf_status`
- `gui_showcase_8k_perf_reason`
- `gui_showcase_8k_perf_backend`
- `gui_showcase_8k_perf_alias_raw_rt_count`
- `gui_showcase_8k_perf_simple_bin_source`
- `gui_showcase_8k_perf_native_build_mode`
- `gui_showcase_8k_perf_fallback_state`

## Failure Semantics

`invalid-4k-backend:wrong-backend` and
`invalid-8k-backend:wrong-backend` mean the aggregate rejected a retained row
because it did not come from the canonical retained widget showcase backend.
Those failures are expected in the negative fixtures.

`met-200fps` and `met-target-fps` mean the aggregate accepted the controlled
row and repaired a stale failure reason after all proof fields passed. Those
success reasons are required by the top-level completion criteria so a
contradictory `status=pass` plus `missing-required-...` row cannot slip through.

## Completion Boundary

Passing this spec proves only aggregate normalization behavior. It does not
prove the real 4K or 8K retained GUI showcase meets 200 FPS on a live host.
The full goal still requires current-source retained perf evidence from the
canonical wrapper and all platform rendering gates in
`gui_web_2d_goal_completion_criteria_spec.spl`.

## Scenarios

### GUI showcase perf backend contract

#### rejects retained 4K and 8K rows with non-canonical backend labels

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects retained 4K and 8K rows with non-canonical backend labels
- Create and aggregate a retained 4K row with a wrong backend
- Create and aggregate a retained 8K row with a wrong backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects retained 4K and 8K rows with non-canonical backend labels")
step("Create and aggregate a retained 4K row with a wrong backend")
val command_4k = retained_4k_backend_command("build/test-gui-showcase-perf-backend-contract-4k")
val (_stdout_4k, _stderr_4k, code_4k) = process_run("/bin/sh", ["-c", command_4k])
# NOTE (2026-08-07, T18): do NOT assert the wrapper's overall process
# exit code here. check-gui-renderdoc-feature-coverage-status.shs is a
# whole-repo aggregate gate that exits non-zero whenever ANY of its many
# unrelated evidence categories (widget-kind coverage, layout manifest,
# etc.) is incomplete -- which this synthetic single-row fixture always
# leaves incomplete. That is correct behavior of the aggregate gate, not
# a defect; the contract this spec tests is captured entirely in
# evidence.env below, which the wrapper writes before it exits non-zero.
# See doc/08_tracking/bug/gui_showcase_source_revision_spec_asserted_wrong_exit_code_2026-08-07.md.
val evidence_4k = file_read("build/test-gui-showcase-perf-backend-contract-4k/out/evidence.env")
expect(evidence_4k).to_contain("gui_showcase_4k_200fps_status=fail")
expect(evidence_4k).to_contain("gui_showcase_4k_200fps_reason=invalid-4k-backend:wrong-backend")

step("Create and aggregate a retained 8K row with a wrong backend")
val command_8k = retained_8k_backend_command("build/test-gui-showcase-perf-backend-contract-8k")
val (_stdout_8k, _stderr_8k, code_8k) = process_run("/bin/sh", ["-c", command_8k])
# See the 4K case above for why the wrapper's overall exit code is not
# asserted here.
val evidence_8k = file_read("build/test-gui-showcase-perf-backend-contract-8k/out/evidence.env")
expect(evidence_8k).to_contain("gui_showcase_8k_perf_status=fail")
expect(evidence_8k).to_contain("gui_showcase_8k_perf_reason=invalid-8k-backend:wrong-backend")
```

</details>

#### normalizes stale retained success reasons after all retained proof gates pass

- normalizes stale retained success reasons after all retained proof gates pass
- Aggregate retained 4K and 8K pass rows that still carry stale missing-evidence reasons


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normalizes stale retained success reasons after all retained proof gates pass")
step("Aggregate retained 4K and 8K pass rows that still carry stale missing-evidence reasons")
val command = retained_success_reason_command("build/test-gui-showcase-perf-success-reason-contract")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
# NOTE (2026-08-07, T18): do NOT assert the wrapper's overall process
# exit code here -- see the 4K/8K cases above.

val evidence = file_read("build/test-gui-showcase-perf-success-reason-contract/out/evidence.env")
expect(evidence).to_contain("gui_showcase_4k_200fps_status=pass")
expect(evidence).to_contain("gui_showcase_4k_200fps_reason=met-200fps")
expect(evidence).to_contain("gui_showcase_8k_perf_status=pass")
expect(evidence).to_contain("gui_showcase_8k_perf_reason=met-target-fps")
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2b89303fe2df4066432e56ff8db6272f7ac3fcf52ff03b194abab57e8ee2d956`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2b89303fe2df4066432e56ff8db6272f7ac3fcf52ff03b194abab57e8ee2d956`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2b89303fe2df4066432e56ff8db6272f7ac3fcf52ff03b194abab57e8ee2d956`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/check/gui_showcase_perf_backend_contract_spec.spl
mirror: doc/06_spec/03_system/check/gui_showcase_perf_backend_contract_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/gui_showcase_perf_backend_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/gui_showcase_perf_backend_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/gui_showcase_perf_backend_contract_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects retained 4K and 8K rows with non-canonical backend labels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_showcase_perf_backend_contract_spec.spl:175:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes stale retained success reasons after all retained proof gates pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
