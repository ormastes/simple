# GUI/Web/2D Parallel Agent Review Evidence

> Verifies the headless-safe checker that turns the parallel-agent plan into machine-readable evidence. The checker must prove that Spark was attempted, quota failures are not counted as completed Spark work, mini fallback sidecars exist, and normal/high-capability review accepted any broad findings before they can influence completion claims.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI/Web/2D Parallel Agent Review Evidence

Verifies the headless-safe checker that turns the parallel-agent plan into machine-readable evidence. The checker must prove that Spark was attempted, quota failures are not counted as completed Spark work, mini fallback sidecars exist, and normal/high-capability review accepted any broad findings before they can influence completion claims.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_web_2d_parallel_agent_review_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the headless-safe checker that turns the parallel-agent plan into
machine-readable evidence. The checker must prove that Spark was attempted,
quota failures are not counted as completed Spark work, mini fallback sidecars
exist, and normal/high-capability review accepted any broad findings before
they can influence completion claims.

**Plan:** doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

This SSpec does not start Spark, mini, or high-model agents. It validates the
recorded review contract and failure behavior of
`scripts/check/check-gui-web-2d-parallel-agent-review-evidence.shs`.

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_web_2d_parallel_agent_review_evidence_spec.spl --mode=interpreter --clean --fail-fast
sh scripts/check/check-gui-web-2d-parallel-agent-review-evidence.shs
```

## Evidence Boundary

A pass here means the parallel-agent plan has source-level evidence that Spark
attempts, fallback sidecars, normal/high-capability review, accepted split
boundaries, and anti-overclaim rules are recorded. It is not live platform,
renderer, or performance evidence.

## Review Workflow

1. Try Spark for read-only evidence-gap and wrapper/key-matrix lanes when quota
   allows.
2. If Spark quota is unavailable, record the failed Spark attempt and start
   mini fallback sidecars for the same read-only questions.
3. Treat Spark and mini findings as advisory until the main agent or a
   normal/high-capability reviewer accepts or rejects the specific findings.
4. Keep platform completion claims blocked until fresh aggregate evidence,
   RenderDoc or native GPU-capture evidence, render-log comparison, full CSS
   closure, production GUI/Web parity, retained 4K/8K freshness, and
   cross-platform freshness all pass.

## Evidence Keys

The checker writes these rows to `evidence.env`:

| Key | Required meaning |
|-----|------------------|
| `gui_web_2d_parallel_agent_review_status` | Overall source-level review contract status |
| `gui_web_2d_parallel_agent_review_reason` | `pass` or the first failure category |
| `gui_web_2d_parallel_agent_review_plan_file_status` | Plan file exists and is readable |
| `gui_web_2d_parallel_agent_review_spark_attempt_status` | Spark attempt or quota-blocked attempt is recorded |
| `gui_web_2d_parallel_agent_review_spark_attempt_count` | Count of `gpt-5.3-codex-spark` records in the plan |
| `gui_web_2d_parallel_agent_review_fallback_sidecar_status` | Mini fallback sidecars are recorded when Spark is unavailable |
| `gui_web_2d_parallel_agent_review_normal_review_status` | Normal/high-capability review lane is recorded |
| `gui_web_2d_parallel_agent_review_accepted_split_status` | Linux Vulkan, macOS Metal, and Windows D3D12 split boundaries are accepted |
| `gui_web_2d_parallel_agent_review_anti_overclaim_status` | Spark/fallback output cannot become completion proof by itself |
| `gui_web_2d_parallel_agent_review_reviewed_findings_status` | Accepted findings remain tied to normal/high-capability review |

## Failure Interpretation

- `parallel-agent-plan-missing` means the plan path is absent and no sidecar
  review contract can be trusted.
- `parallel-agent-review-evidence-incomplete` means one or more source-level
  review contract checks failed. The failed per-key status identifies whether
  Spark attempts, fallback sidecars, normal review, split acceptance,
  anti-overclaim rules, or reviewed findings need repair.
- A passing status does not prove any platform renderer row. It only proves
  the review-control surface is present and fail-closed.

## Completion Boundary Checklist

- Spark quota failures are valid attempts, not completed Spark work.
- Mini fallback findings are advisory until reviewed.
- Normal/high-capability review is required before broad findings are accepted.
- Platform rows remain incomplete until live host artifacts prove them.
- A source-level pass from this checker must not reduce the remaining live-gate
  count emitted by the headless handoff wrapper.

## Manual Run Steps

1. Run this SSpec to validate the checker pass path and missing-plan fail path.
2. Run `sh scripts/check/check-gui-web-2d-parallel-agent-review-evidence.shs`
   directly when updating the parallel-agent plan.
3. Confirm the report lists Spark attempts, fallback sidecars,
   normal/high-capability review, accepted split boundaries, anti-overclaim
   rules, and reviewed findings as `pass`.
4. Confirm any failed checker output is treated as a plan/control failure, not
   as renderer evidence.
5. Confirm final goal completion is still blocked until the live platform gates
   named by the headless handoff wrapper have fresh evidence.

## Acceptance

- The checker emits pass evidence for Spark-attempt, fallback-sidecar,
  normal-review, accepted-split, anti-overclaim, and reviewed-finding gates.
- The checker records Spark quota failures as attempts, not completed Spark
  output.
- The checker fails closed when the plan file is missing.
- The generated report includes the raw evidence rows needed by future agents.

## Scenarios

### GUI/Web/2D parallel-agent review evidence

#### runs the review evidence checker without claiming live renderer completion

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs the review evidence checker without claiming live renderer completion
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs the review evidence checker without claiming live renderer completion")
val command = "rm -rf build/test-gui-web-2d-parallel-agent-review && BUILD_DIR=build/test-gui-web-2d-parallel-agent-review/out REPORT_PATH=build/test-gui-web-2d-parallel-agent-review/report.md sh scripts/check/check-gui-web-2d-parallel-agent-review-evidence.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-gui-web-2d-parallel-agent-review/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_parallel_agent_review_status=pass")
expect(evidence).to_contain("gui_web_2d_parallel_agent_review_reason=pass")
expect(evidence).to_contain("gui_web_2d_parallel_agent_review_plan_file_status=pass")
expect(evidence).to_contain("gui_web_2d_parallel_agent_review_spark_attempt_status=pass")
expect(evidence).to_contain("gui_web_2d_parallel_agent_review_fallback_sidecar_status=pass")
expect(evidence).to_contain("gui_web_2d_parallel_agent_review_normal_review_status=pass")
expect(evidence).to_contain("gui_web_2d_parallel_agent_review_accepted_split_status=pass")
expect(evidence).to_contain("gui_web_2d_parallel_agent_review_anti_overclaim_status=pass")
expect(evidence).to_contain("gui_web_2d_parallel_agent_review_reviewed_findings_status=pass")

val report = file_read("build/test-gui-web-2d-parallel-agent-review/report.md")
expect(report).to_contain("# GUI/Web/2D Parallel Agent Review Evidence")
expect(report).to_contain("- Spark attempt: pass")
expect(report).to_contain("- fallback sidecars: pass")
expect(report).to_contain("- normal/high-capability review: pass")
expect(report).to_contain("- accepted platform split: pass")
expect(report).to_contain("- anti-overclaim rules: pass")
```

</details>

#### fails closed when the parallel-agent plan is missing

- fails closed when the parallel-agent plan is missing
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed when the parallel-agent plan is missing")
val command = "rm -rf build/test-gui-web-2d-parallel-agent-review-missing && GUI_WEB_2D_PARALLEL_AGENT_PLAN=build/test-gui-web-2d-parallel-agent-review-missing/missing-plan.md BUILD_DIR=build/test-gui-web-2d-parallel-agent-review-missing/out REPORT_PATH=build/test-gui-web-2d-parallel-agent-review-missing/report.md sh scripts/check/check-gui-web-2d-parallel-agent-review-evidence.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read("build/test-gui-web-2d-parallel-agent-review-missing/out/evidence.env")
expect(evidence).to_contain("gui_web_2d_parallel_agent_review_status=fail")
expect(evidence).to_contain("gui_web_2d_parallel_agent_review_reason=parallel-agent-plan-missing")
expect(evidence).to_contain("gui_web_2d_parallel_agent_review_plan_file_status=missing")
expect(evidence).to_contain("gui_web_2d_parallel_agent_review_spark_attempt_status=fail")
expect(evidence).to_contain("gui_web_2d_parallel_agent_review_fallback_sidecar_status=fail")
expect(evidence).to_contain("gui_web_2d_parallel_agent_review_normal_review_status=fail")
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

- **Plan:** `doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md`
- **Design:** `doc/07_guide/tooling/renderdoc_capture_infra.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c61b62f4e5ee2fcb7b8128cb2be16abca7de55ce6bbfdd7a49f2c1b2e85acc37`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c61b62f4e5ee2fcb7b8128cb2be16abca7de55ce6bbfdd7a49f2c1b2e85acc37`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c61b62f4e5ee2fcb7b8128cb2be16abca7de55ce6bbfdd7a49f2c1b2e85acc37`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/check/gui_web_2d_parallel_agent_review_evidence_spec.spl
mirror: doc/06_spec/03_system/check/gui_web_2d_parallel_agent_review_evidence_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/gui_web_2d_parallel_agent_review_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/gui_web_2d_parallel_agent_review_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/gui_web_2d_parallel_agent_review_evidence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/gui_web_2d_parallel_agent_review_evidence_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs the review evidence checker without claiming live renderer completion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_web_2d_parallel_agent_review_evidence_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when the parallel-agent plan is missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
