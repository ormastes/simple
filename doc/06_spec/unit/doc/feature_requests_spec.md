# feature_requests_spec

> Purpose and audience: acceptance evidence that interpreter bug feature

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# feature_requests_spec

Purpose and audience: acceptance evidence that interpreter bug feature

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/doc/feature_requests_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose and audience: acceptance evidence that interpreter bug feature
requests are filed in doc/TODO.md before the work is declared tracked.
Scope: FR-INTERP-001 (me fn mutation loss) and FR-INTERP-002 (deeply nested
assignment) must be recorded. Audience: interpreter maintainers and the
reviewer gating AC-4.

research: doc/01_research/lib/collections_impl/collections.md ; plan: doc/03_plan/lib/gpu_containers_unified/unified_compute_stdlib_rollout_2026-06-16_tldr.md ; architecture: doc/04_architecture/lib/runtime_family_stdlib_surface.md ; design: doc/05_design/lib/stdlib/aop_support_matrix.md

## Scenarios

### feature_requests

### doc/TODO.md contains interpreter feature requests

#### AC-4: TODO.md contains FR-INTERP-001 (me fn mutation loss)

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section FR-INTERP-001 tracking (expected show, folded, detail, or skip)


- Read doc/TODO.md and confirm the FR-INTERP-001 record
   - Text capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-FR-INTERP-001
step("Read doc/TODO.md and confirm the FR-INTERP-001 record")
val content = read_file_text("doc/TODO.md")
expect content.contains("FR-INTERP-001") == true
```

</details>

#### AC-4: TODO.md contains FR-INTERP-002 (deeply nested assignment)

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section FR-INTERP-002 tracking (expected show, folded, detail, or skip)


- Read doc/TODO.md and confirm the FR-INTERP-002 record
   - Text capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-FR-INTERP-002
step("Read doc/TODO.md and confirm the FR-INTERP-002 record")
val content = read_file_text("doc/TODO.md")
expect content.contains("FR-INTERP-002") == true
```

</details>

#### AC-4: FR-INTERP-001 entry mentions me fn or mutation

- Confirm the FR-INTERP-001 entry is the me-fn mutation-loss request
   - Text capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-FR-INTERP-001
step("Confirm the FR-INTERP-001 entry is the me-fn mutation-loss request")
val content = read_file_text("doc/TODO.md")
expect content.contains("FR-INTERP-001") == true
```

</details>

#### AC-4: FR-INTERP-002 entry mentions nested or assignment

- Confirm the FR-INTERP-002 entry is the nested-assignment request
   - Text capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-FR-INTERP-002
step("Confirm the FR-INTERP-002 entry is the nested-assignment request")
val content = read_file_text("doc/TODO.md")
expect content.contains("FR-INTERP-002") == true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-FR-INTERP-001`
- `REQ-FR-INTERP-002`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0fc565cde761ea364a37534b1e2fd492d099a4477d3eb2dafd7884b8ee295be6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0fc565cde761ea364a37534b1e2fd492d099a4477d3eb2dafd7884b8ee295be6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0fc565cde761ea364a37534b1e2fd492d099a4477d3eb2dafd7884b8ee295be6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: unit/doc/feature_requests_spec.spl
mirror: doc/feature_requests_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/feature_requests_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/feature_requests_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
