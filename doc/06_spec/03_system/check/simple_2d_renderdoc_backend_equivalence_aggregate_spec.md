# Simple 2D RenderDoc Backend Equivalence Aggregate

> Reports every profile, backend, corpus, QEMU, SIMD, board, artifact, timing,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple 2D RenderDoc Backend Equivalence Aggregate

Reports every profile, backend, corpus, QEMU, SIMD, board, artifact, timing,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/simple_2d_renderdoc_backend_equivalence_aggregate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Reports every profile, backend, corpus, QEMU, SIMD, board, artifact, timing,
memory, and blocker row without promoting unavailable evidence.

## Scenarios

### Backend equivalence aggregate

#### rejects unavailable runtime and capture inputs without hiding rows

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects unavailable runtime and capture inputs without hiding rows
   - Exec capture: after_step
- Calibrate the aggregate fail-closed contract
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects unavailable runtime and capture inputs without hiding rows")
step("Calibrate the aggregate fail-closed contract")
val (_stdout, _stderr, code) = process_run(
    "/bin/sh",
    ["scripts/check/check-simple-2d-renderdoc-backend-equivalence.shs", "--self-test"]
)
expect(code).to_equal(0)
expect(_stdout).to_contain("simple_renderdoc_aggregate_self_test_status=pass")
```

</details>

#### reports focused rows timing RSS blockers and requirement traceability

- reports focused rows timing RSS blockers and requirement traceability
   - Exec capture: after_step
- Run the focused profile once
   - Exec capture: after_step
- Inspect every retained host and backend row
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: value_of(evidence, "simple_renderdoc_aggregate_profile") equals `focused`
- Require a pass or a typed nonempty blocker collection
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: code equals `0`
   - Expected: value_of(evidence, "simple_renderdoc_aggregate_profile_blocker_count") equals `0`
   - Expected: status equals `blocked`
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports focused rows timing RSS blockers and requirement traceability")
step("Run the focused profile once")
val root = "build/test-simple-2d-renderdoc-backend-equivalence"
val command = "BUILD_DIR=" + root + "/out REPORT_PATH=" + root +
    "/report.md sh scripts/check/check-simple-2d-renderdoc-backend-equivalence.shs --profile=focused"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_be_less_than(2)

step("Inspect every retained host and backend row")
val evidence = file_read(root + "/out/evidence.env")
expect(value_of(evidence, "simple_renderdoc_aggregate_schema")).to_equal(
    "simple-renderdoc-aggregate-v1")
expect(value_of(evidence, "simple_renderdoc_aggregate_profile")).to_equal("focused")
expect(value_of(evidence, "simple_renderdoc_aggregate_row_count").to_i64()).to_be_greater_than(0)
expect(evidence).to_contain("_elapsed_ms=")
expect(evidence).to_contain("_max_rss_kb=")
expect(evidence).to_contain("_requirements=")
expect(evidence).to_contain("simple_renderdoc_aggregate_simpleos_simd_status=")
expect(evidence).to_contain("simple_renderdoc_aggregate_windows_d3d11_d3d12_status=")
expect(evidence).to_contain("simple_renderdoc_aggregate_macos_metal_status=")
expect(evidence).to_contain("simple_renderdoc_aggregate_physical_boards_status=")

step("Require a pass or a typed nonempty blocker collection")
val status = value_of(evidence, "simple_renderdoc_aggregate_status")
if status == "pass":
    expect(code).to_equal(0)
    expect(value_of(evidence, "simple_renderdoc_aggregate_profile_blocker_count")).to_equal("0")
else:
    expect(status).to_equal("blocked")
    expect(code).to_equal(1)
    expect(value_of(evidence, "simple_renderdoc_aggregate_profile_blocker_count").to_i64()).to_be_greater_than(0)
    expect(value_of(evidence, "simple_renderdoc_aggregate_blocker_keys").len()).to_be_greater_than(0)
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

- `REQ-SSPEC-SYSTEM`
- `REQ-013`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `87c3a4a3386aa55770897305260a1543f2c4457e2b7d4b8adfa574bd61e7ee86`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `87c3a4a3386aa55770897305260a1543f2c4457e2b7d4b8adfa574bd61e7ee86`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `87c3a4a3386aa55770897305260a1543f2c4457e2b7d4b8adfa574bd61e7ee86`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/check/simple_2d_renderdoc_backend_equivalence_aggregate_spec.spl
mirror: doc/06_spec/03_system/check/simple_2d_renderdoc_backend_equivalence_aggregate_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/check/simple_2d_renderdoc_backend_equivalence_aggregate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/simple_2d_renderdoc_backend_equivalence_aggregate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/simple_2d_renderdoc_backend_equivalence_aggregate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/simple_2d_renderdoc_backend_equivalence_aggregate_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/check/simple_2d_renderdoc_backend_equivalence_aggregate_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unavailable runtime and capture inputs without hiding rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/simple_2d_renderdoc_backend_equivalence_aggregate_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports focused rows timing RSS blockers and requirement traceability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
