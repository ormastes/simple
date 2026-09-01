# Claude Full path utils

> Pure Simple coverage for path traversal segment detection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full path utils

Pure Simple coverage for path traversal segment detection.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/path_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for path traversal segment detection.

## Scenarios

### Claude full path utils

#### detects parent-directory traversal as a path segment

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects parent-directory traversal as a path segment
- Reject traversal segments
   - Expected: containsPathTraversal("../secret") is true
   - Expected: containsPathTraversal("..") is true
   - Expected: containsPathTraversal("safe/../secret") is true
   - Expected: containsPathTraversal("safe\\..\\secret") is true
   - Expected: containsPathTraversal("safe/..\\secret") is true
   - Expected: containsPathTraversal("safe\\../secret") is true
   - Expected: containsPathTraversal("safe/..") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects parent-directory traversal as a path segment")
step("Reject traversal segments")
expect(containsPathTraversal("../secret")).to_equal(true)
expect(containsPathTraversal("..")).to_equal(true)
expect(containsPathTraversal("safe/../secret")).to_equal(true)
expect(containsPathTraversal("safe\\..\\secret")).to_equal(true)
expect(containsPathTraversal("safe/..\\secret")).to_equal(true)
expect(containsPathTraversal("safe\\../secret")).to_equal(true)
expect(containsPathTraversal("safe/..")).to_equal(true)
```

</details>

#### allows dotted names that are not standalone traversal segments

- allows dotted names that are not standalone traversal segments
- Allow non-traversal dots
   - Expected: containsPathTraversal("safe/..hidden/file") is false
   - Expected: containsPathTraversal("safe/.../file") is false
   - Expected: containsPathTraversal("safe/file..txt") is false
   - Expected: containsPathTraversal("safe/file") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows dotted names that are not standalone traversal segments")
step("Allow non-traversal dots")
expect(containsPathTraversal("safe/..hidden/file")).to_equal(false)
expect(containsPathTraversal("safe/.../file")).to_equal(false)
expect(containsPathTraversal("safe/file..txt")).to_equal(false)
expect(containsPathTraversal("safe/file")).to_equal(false)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0c896e8215e9a80e917c3cb53728746915261c14eb1f4b036c16678cdaeac525`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0c896e8215e9a80e917c3cb53728746915261c14eb1f4b036c16678cdaeac525`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0c896e8215e9a80e917c3cb53728746915261c14eb1f4b036c16678cdaeac525`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/app/llm_caret/path_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/path_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/path_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/path_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/path_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects parent-directory traversal as a path segment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/path_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows dotted names that are not standalone traversal segments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
