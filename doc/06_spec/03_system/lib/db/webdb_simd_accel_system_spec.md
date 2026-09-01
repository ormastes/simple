# webdb_simd_accel_system_spec

> Verifies the web/db server's accelerated scan path returns correct rows

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# webdb_simd_accel_system_spec

Verifies the web/db server's accelerated scan path returns correct rows

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/03_system/lib/db/webdb_simd_accel_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies the web/db server's accelerated scan path returns correct rows
    against a hand-verified oracle, and that its capability report cannot
    silently overclaim SIMD acceleration it did not actually run.

## Scenarios

### Web/DB server SIMD acceleration

#### returns exactly the rows matching the predicate, not merely a self-consistent set

- returns exactly the rows matching the predicate, not merely a self-consistent set
- Load a fixed corpus whose matching rows are known by hand
   - Expected: corpus.len() equals `6`
- Run the accelerated prefix scan the server's query path uses
- Compare against the absolute oracle, not against another scan
   - Expected: rows.len() equals `expected.len()`
   - Expected: rows.len() equals `3`
   - Expected: rows[idx] equals `expected[idx]`
- Confirm the scan actually walked every row rather than short-circuiting
   - Expected: stats.rows_scanned equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns exactly the rows matching the predicate, not merely a self-consistent set")
step("Load a fixed corpus whose matching rows are known by hand")
val corpus = accel_corpus()
expect(corpus.len()).to_equal(6)

step("Run the accelerated prefix scan the server's query path uses")
val predicate = ScanPredicate(
    kind: ScanPredicateKind.StartsWith,
    text_value: "src/",
    key_value: 0
)
val (rows, stats) = collect_text_row_indices(corpus, predicate)

step("Compare against the absolute oracle, not against another scan")
val expected = expected_src_rows()
expect(rows.len()).to_equal(expected.len())
expect(rows.len()).to_equal(3)
var idx = 0
while idx < expected.len():
    expect(rows[idx]).to_equal(expected[idx])
    idx = idx + 1

step("Confirm the scan actually walked every row rather than short-circuiting")
expect(stats.rows_scanned).to_equal(6)
```

</details>

#### reports a capability set that cannot silently overclaim acceleration

- reports a capability set that cannot silently overclaim acceleration
- Read the acceleration capability report the server exposes
- Confirm the reported SIMD tier agrees with what the host actually detects
   - Expected: report.tier_name equals `profile_name()`
- Confirm active-implies-available: claiming to run SIMD that is not there is the fraud
- Confirm active and scalar_fallback are not both asserted at once


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports a capability set that cannot silently overclaim acceleration")
step("Read the acceleration capability report the server exposes")
val report = accel_capability_report()

step("Confirm the reported SIMD tier agrees with what the host actually detects")
expect(report.tier_name).to_equal(profile_name())
val tier = detect_profile()
val detected_available = match tier:
    case SimdTier.scalar: false
    case _: true
expect(report.simd_available).to_be(detected_available)

step("Confirm active-implies-available: claiming to run SIMD that is not there is the fraud")
if report.simd_active:
    assert_true(report.simd_available)

step("Confirm active and scalar_fallback are not both asserted at once")
if report.simd_active:
    expect_not(report.scalar_fallback)
```

</details>

#### records that db SIMD dispatch is detected but not yet activated

- records that db SIMD dispatch is detected but not yet activated
- Read the capability report
- Assert the honest current state: detection works, dispatch is not wired
- Assert the width is still reported so the wiring work has a target


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records that db SIMD dispatch is detected but not yet activated")
# Pins the measured 2026-08-11 gap so a future wiring change is a DELIBERATE
# edit here with evidence, not a silent flip of a boolean in the library.
step("Read the capability report")
val report = accel_capability_report()

step("Assert the honest current state: detection works, dispatch is not wired")
expect_not(report.simd_active)
assert_true(report.scalar_fallback)

step("Assert the width is still reported so the wiring work has a target")
expect(report.simd_width_bits).to_be_greater_than(0)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1752ac1a7a3463a0b5e98168a42c194576e4f2ec0d5db885d2e37d1409fb7d51`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1752ac1a7a3463a0b5e98168a42c194576e4f2ec0d5db885d2e37d1409fb7d51`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1752ac1a7a3463a0b5e98168a42c194576e4f2ec0d5db885d2e37d1409fb7d51`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/lib/db/webdb_simd_accel_system_spec.spl
mirror: doc/06_spec/03_system/lib/db/webdb_simd_accel_system_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/lib/db/webdb_simd_accel_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/lib/db/webdb_simd_accel_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/lib/db/webdb_simd_accel_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/lib/db/webdb_simd_accel_system_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns exactly the rows matching the predicate, not merely a self-consistent set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/lib/db/webdb_simd_accel_system_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a capability set that cannot silently overclaim acceleration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/lib/db/webdb_simd_accel_system_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records that db SIMD dispatch is detected but not yet activated' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
