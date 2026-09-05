# formula_spill_origin_spec

> Spill-origin numeric aggregation spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_spill_origin_spec

Spill-origin numeric aggregation spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_spill_origin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Spill-origin numeric aggregation spec.

Regression spec for doc/08_tracking/bug/
formula_spill_origin_drop_in_numeric_path_2026-07-04.md: the origin cell of a
dynamic-array spill stays a FormulaVal, and `_resolve_cell_value` used to
re-evaluate it through the SCALAR path — where array-registered functions
(SEQUENCE/MMULT/...) have no handler — so the origin contributed 0 to
SUM/AVERAGE over its own spill range (=SUM over a SEQUENCE(2,2) spill gave 9,
not 10). The fix prefers the numeric parse of `cached_display` for FormulaVal
cells whose expression evaluate_formula_array recognizes (non-empty grid).

Ground truth (hand-computed):
- SEQUENCE(2,2) spills 1 2 / 3 4 → SUM 10, AVERAGE 2.5.
- MMULT(A1:B2,A1:B2) on the fixture A1=10 A2=20 B1=30 B2=40, i.e. rows
  [10,30],[20,40]: [[10*10+30*20, 10*30+30*40],[20*10+40*20, 20*30+40*40]]
  = [[700,1500],[1000,2200]] → SUM 5400.
- OFFSET(A1,0,0,2,2) spills 10 30 / 20 40 → SUM 100 (OFFSET is on BOTH the
  scalar and array paths; its cached origin display equals the scalar
  top-left, so the total must stay 100 after the fix).
- A plain scalar formula origin (=1+1) in a summed range contributes 2 —
  the non-array path is unchanged.

## Scenarios

### spill-origin cell in numeric aggregation

#### SUM over a SEQUENCE(2,2) spill totals 10 (origin contributes 1, not 0)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- SUM over a SEQUENCE(2,2) spill totals 10 (origin contributes 1, not 0)
   - Expected: _spill_then("=SEQUENCE(2,2)", "=SUM(D1:E2)") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SUM over a SEQUENCE(2,2) spill totals 10 (origin contributes 1, not 0)")
expect(_spill_then("=SEQUENCE(2,2)", "=SUM(D1:E2)")).to_equal("10")
```

</details>

#### AVERAGE over a SEQUENCE(2,2) spill is 2.5

- AVERAGE over a SEQUENCE(2,2) spill is 2.5
   - Expected: _spill_then("=SEQUENCE(2,2)", "=AVERAGE(D1:E2)") equals `2.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AVERAGE over a SEQUENCE(2,2) spill is 2.5")
expect(_spill_then("=SEQUENCE(2,2)", "=AVERAGE(D1:E2)")).to_equal("2.5")
```

</details>

#### SUM over an MMULT(A1:B2,A1:B2) spill totals 5400 (700+1500+1000+2200)

- SUM over an MMULT(A1:B2,A1:B2) spill totals 5400 (700+1500+1000+2200)
   - Expected: _spill_then("=MMULT(A1:B2,A1:B2)", "=SUM(D1:E2)") equals `5400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SUM over an MMULT(A1:B2,A1:B2) spill totals 5400 (700+1500+1000+2200)")
expect(_spill_then("=MMULT(A1:B2,A1:B2)", "=SUM(D1:E2)")).to_equal("5400")
```

</details>

#### SUM over an OFFSET(A1,0,0,2,2) spill still totals 100 (dual-path fn)

- SUM over an OFFSET(A1,0,0,2,2) spill still totals 100 (dual-path fn)
   - Expected: _spill_then("=OFFSET(A1,0,0,2,2)", "=SUM(D1:E2)") equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SUM over an OFFSET(A1,0,0,2,2) spill still totals 100 (dual-path fn)")
expect(_spill_then("=OFFSET(A1,0,0,2,2)", "=SUM(D1:E2)")).to_equal("100")
```

</details>

#### OFFSET spill origin display equals the scalar top-left (both sources agree)

- OFFSET spill origin display equals the scalar top-left (both sources agree)
   - Expected: _disp(sh, "D1") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("OFFSET spill origin display equals the scalar top-left (both sources agree)")
var sh = Sheet.new("f")
sh = _base(sh)
sh.set_value("D1", "=OFFSET(A1,0,0,2,2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("10")
```

</details>

#### a plain scalar formula origin (=1+1) still contributes 2 to SUM

- a plain scalar formula origin (=1+1) still contributes 2 to SUM
   - Expected: _disp(sh, "G1") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a plain scalar formula origin (=1+1) still contributes 2 to SUM")
var sh = Sheet.new("f")
sh.set_value("A1", "3")
sh.set_value("B1", "4")
sh.set_value("C1", "=1+1")
sh = recalculate_formula_cells(sh)
sh.set_value("G1", "=SUM(A1:C1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "G1")).to_equal("9")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `705d3a6a4739ef2df3a7cc9c5ff9752da8aef15d4391210525691008bf7727d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `705d3a6a4739ef2df3a7cc9c5ff9752da8aef15d4391210525691008bf7727d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `705d3a6a4739ef2df3a7cc9c5ff9752da8aef15d4391210525691008bf7727d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_spill_origin_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_spill_origin_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_spill_origin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_spill_origin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_spill_origin_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SUM over a SEQUENCE(2,2) spill totals 10 (origin contributes 1, not 0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_spill_origin_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AVERAGE over a SEQUENCE(2,2) spill is 2.5' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_spill_origin_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SUM over an MMULT(A1:B2,A1:B2) spill totals 5400 (700+1500+1000+2200)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
