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
| Updated | 2026-08-11 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies the web/db server's accelerated scan path returns correct rows
    against a hand-verified oracle, and that its capability report cannot
    silently overclaim SIMD acceleration it did not actually run.

## Scenarios

### Web/DB server SIMD acceleration

#### returns exactly the rows matching the predicate, not merely a self-consistent set

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

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Read the acceleration capability report the server exposes
- Confirm the reported SIMD tier agrees with what the host actually detects
   - Expected: report.tier_name equals `profile_name()`
- Confirm active-implies-available: claiming to run SIMD that is not there is the fraud
- Confirm active and scalar_fallback are not both asserted at once


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Read the capability report
- Assert the honest current state: detection works, dispatch is not wired
- Assert the width is still reported so the wiring work has a target


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
