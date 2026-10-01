# report_spec

> Access-style grouped report spec — report.spl over table.spl + query.spl.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# report_spec

Access-style grouped report spec — report.spl over table.spl + query.spl.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/database/report_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Access-style grouped report spec — report.spl over table.spl + query.spl.

Ground truth is hand-computed against one small sales table:

sales(region, amount):
  East, 100
  East, 200
  West, 300
  West, 400

Sorted ascending by region ("East" < "West" alphabetically), so groups come
out in that order regardless of insertion order.

sum agg:
  East subtotal = 100 + 200 = 300
  West subtotal = 300 + 400 = 700
  grand total   = 300 + 700 = 1000

avg agg (integer division, exact here):
  East subtotal = 300 / 2 = 150
  West subtotal = 700 / 2 = 350
  grand total   = 1000 / 4 = 250

## Scenarios

### report_grouped: sum aggregate

#### renders group headers, detail lines, subtotals, and a grand total

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders group headers, detail lines, subtotals, and a grand total


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders group headers, detail lines, subtotals, and a grand total")
val t = _sales()
val r = report_grouped(t, "region", "amount", "sum")
expect(r).to_contain("== East ==")
expect(r).to_contain("== West ==")
expect(r).to_contain("  East: 100")
expect(r).to_contain("  West: 400")
expect(r).to_contain("  subtotal: 300")
expect(r).to_contain("  subtotal: 700")
expect(r).to_contain("TOTAL: 1000")
```

</details>

#### matches the exact hand-computed report text

- matches the exact hand-computed report text
   - Expected: r equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("matches the exact hand-computed report text")
val t = _sales()
val r = report_grouped(t, "region", "amount", "sum")
val expected = [
    "== East ==",
    "  East: 100",
    "  East: 200",
    "  subtotal: 300",
    "== West ==",
    "  West: 300",
    "  West: 400",
    "  subtotal: 700",
    "TOTAL: 1000",
].join("\n")
expect(r).to_equal(expected)
```

</details>

### report_grouped: avg aggregate

#### matches the exact hand-computed integer-average report text

- matches the exact hand-computed integer-average report text
   - Expected: r equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("matches the exact hand-computed integer-average report text")
val t = _sales()
val r = report_grouped(t, "region", "amount", "avg")
val expected = [
    "== East ==",
    "  East: 100",
    "  East: 200",
    "  subtotal: 150",
    "== West ==",
    "  West: 300",
    "  West: 400",
    "  subtotal: 350",
    "TOTAL: 250",
].join("\n")
expect(r).to_equal(expected)
```

</details>

### report_to_html

#### renders section/h3/subtotal/grand-total markup with escaped detail rows

- renders section/h3/subtotal/grand-total markup with escaped detail rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders section/h3/subtotal/grand-total markup with escaped detail rows")
val t = _sales()
val h = report_to_html(t, "region", "amount", "sum")
expect(h).to_contain("<section><h3>East</h3><ul>")
expect(h).to_contain("<section><h3>West</h3><ul>")
expect(h).to_contain("<li>East: 100</li>")
expect(h).to_contain("<li>West: 400</li>")
expect(h).to_contain("<p class=\"subtotal\">subtotal: 300</p>")
expect(h).to_contain("<p class=\"subtotal\">subtotal: 700</p>")
expect(h).to_contain("<footer class=\"grand-total\">TOTAL: 1000</footer>")
```

</details>

### tail execution probe

#### confirms the final describe block actually runs

- confirms the final describe block actually runs
   - Expected: 1 + 1 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("confirms the final describe block actually runs")
expect(1 + 1).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `04024adb9e0f2c511cdbb3c43d024b5b16197a5829b8b3ff3de59cd3f8c88c1e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `04024adb9e0f2c511cdbb3c43d024b5b16197a5829b8b3ff3de59cd3f8c88c1e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `04024adb9e0f2c511cdbb3c43d024b5b16197a5829b8b3ff3de59cd3f8c88c1e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/office/database/report_spec.spl
mirror: doc/06_spec/01_unit/app/office/database/report_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/database/report_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/database/report_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/database/report_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/office/database/report_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders group headers, detail lines, subtotals, and a grand total' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/database/report_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the exact hand-computed report text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/database/report_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the exact hand-computed integer-average report text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
