# engine2d_vulkan_window_8k_receipt_spec

> Vulkan 8K window receipt parsing and physical-admission contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# engine2d_vulkan_window_8k_receipt_spec

Vulkan 8K window receipt parsing and physical-admission contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/engine2d_vulkan_window_8k_receipt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Vulkan 8K window receipt parsing and physical-admission contract.

## Scenarios

### Engine2D Vulkan 8K window receipt

#### normalizes Cargo output and rejects weak physical displays

- Run the checker self-test without opening a display
- Require strict receipt and EDID parsing
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the checker self-test without opening a display")
# @req: REQ-GPU-DYN-007
val (stdout, _stderr, code) = process_run(
    "/bin/sh",
    ["scripts/check/check-engine2d-vulkan-window-8k.shs", "--self-test"])

step("Require strict receipt and EDID parsing")
expect(code).to_equal(0)
expect(stdout).to_contain("engine2d_vulkan_window_8k_selftest=pass")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-GPU-DYN-007`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b72855e5bf2f692fbbe3e4f2584022806cba05b3cf7121970b93e8384e784b57`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b72855e5bf2f692fbbe3e4f2584022806cba05b3cf7121970b93e8384e784b57`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b72855e5bf2f692fbbe3e4f2584022806cba05b3cf7121970b93e8384e784b57`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/check/engine2d_vulkan_window_8k_receipt_spec.spl
mirror: doc/06_spec/03_system/check/engine2d_vulkan_window_8k_receipt_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=100 oracle=90
  traceability=100 evidence=90 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/engine2d_vulkan_window_8k_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/engine2d_vulkan_window_8k_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/engine2d_vulkan_window_8k_receipt_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/03_system/check/engine2d_vulkan_window_8k_receipt_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/03_system/check/engine2d_vulkan_window_8k_receipt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/engine2d_vulkan_window_8k_receipt_spec.spl:10:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes Cargo output and rejects weak physical displays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
