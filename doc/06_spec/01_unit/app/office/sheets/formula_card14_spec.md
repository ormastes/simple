# formula_card14_spec

> Calc deferred-math remainder spec (CARD 14).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_card14_spec

Calc deferred-math remainder spec (CARD 14).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_card14_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc deferred-math remainder spec (CARD 14).

Every shipped function is pinned to a PUBLISHED Excel worked example, not a
self-derived value:
  * CHISQ.TEST({58,35;11,25;10,23}, {45.35,47.65;17.56,18.44;16.09,16.91})
    = 0.000308  (Excel documentation example; df=(3-1)(2-1)=2).
  * T.TEST({3,4,5,8,9,1,2,4,5},{6,19,3,2,14,4,5,17,1}, 2, 1) = 0.196016
    (Excel documentation example; paired, two-tailed).
  * F.TEST({6,7,9,15,21},{20,28,31,38,40}) = 0.648318 (Excel documentation
    example; var1=39.8, var2=64.8, two-tailed. NOTE: the CARD 14 brief's
    array1 carried five extra elements {26,28,31,38,40} — a plan transcription
    typo of the same kind the card warns about; verified against the genuine
    MS worked example, which is 5-vs-5 and reproduces 0.648318 exactly).
  * BESSELY(2.5,1) = 0.145918 ; BESSELK(1.5,1) = 0.277388 (Excel docs).
Bare ROW()/COLUMN() resolve through the module-level origin var set by the
recalc driver (CARD 14 probe: module-var mutation survives the interpreter on
the imported-module path used by recalculate_formula_cells). A direct
evaluate_formula call with no cell context leaves ROW()/COLUMN() as #ERR.
LET/LAMBDA remain deferred (evaluator variable scoping) — no assertions here.

## Scenarios

### Calc CHISQ.TEST

#### matches the Excel documentation worked example to 6 digits

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the Excel documentation worked example to 6 digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches the Excel documentation worked example to 6 digits")
expect(_run_approx(_chisq_sheet(), "=CHISQ.TEST(A1:B3,D1:E3)", 0.000308, 0.0000005)).to_be(true)
```

</details>

#### aliases the legacy CHITEST spelling

- aliases the legacy CHITEST spelling


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aliases the legacy CHITEST spelling")
expect(_run_approx(_chisq_sheet(), "=CHITEST(A1:B3,D1:E3)", 0.000308, 0.0000005)).to_be(true)
```

</details>

#### errors when the two ranges differ in size

- errors when the two ranges differ in size


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("errors when the two ranges differ in size")
expect(_run(_chisq_sheet(), "=CHISQ.TEST(A1:B3,D1:E2)")).to_contain("#ERR")
```

</details>

### Calc T.TEST

#### paired two-tailed matches the Excel documentation example

- paired two-tailed matches the Excel documentation example


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paired two-tailed matches the Excel documentation example")
expect(_run_approx(_ttest_sheet(), "=T.TEST(A1:A9,B1:B9,2,1)", 0.196016, 0.000001)).to_be(true)
```

</details>

#### one-tailed paired is half the two-tailed probability

- one-tailed paired is half the two-tailed probability


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("one-tailed paired is half the two-tailed probability")
expect(_run_approx(_ttest_sheet(), "=T.TEST(A1:A9,B1:B9,1,1)", 0.098008, 0.000001)).to_be(true)
```

</details>

#### aliases the legacy TTEST spelling

- aliases the legacy TTEST spelling


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aliases the legacy TTEST spelling")
expect(_run_approx(_ttest_sheet(), "=TTEST(A1:A9,B1:B9,2,1)", 0.196016, 0.000001)).to_be(true)
```

</details>

#### two-sample equal-variance (type 2) runs

- two-sample equal-variance (type 2) runs


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two-sample equal-variance (type 2) runs")
expect(_run(_ttest_sheet(), "=T.TEST(A1:A9,B1:B9,2,2)").to_f64() > 0.0).to_be(true)
```

</details>

#### two-sample unequal-variance Welch (type 3) runs

- two-sample unequal-variance Welch (type 3) runs


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two-sample unequal-variance Welch (type 3) runs")
expect(_run(_ttest_sheet(), "=T.TEST(A1:A9,B1:B9,2,3)").to_f64() > 0.0).to_be(true)
```

</details>

### Calc F.TEST

#### matches the Excel documentation worked example to 6 digits

- matches the Excel documentation worked example to 6 digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches the Excel documentation worked example to 6 digits")
expect(_run_approx(_ftest_sheet(), "=F.TEST(A1:A5,B1:B5)", 0.648318, 0.000001)).to_be(true)
```

</details>

#### aliases the legacy FTEST spelling

- aliases the legacy FTEST spelling


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aliases the legacy FTEST spelling")
expect(_run_approx(_ftest_sheet(), "=FTEST(A1:A5,B1:B5)", 0.648318, 0.000001)).to_be(true)
```

</details>

### Calc BESSELY / BESSELK

#### BESSELY(2.5,1) matches the Excel-documented value to 6 digits

- BESSELY(2.5,1) matches the Excel-documented value to 6 digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BESSELY(2.5,1) matches the Excel-documented value to 6 digits")
expect(_approx("=BESSELY(2.5,1)", 0.145918, 0.000001)).to_be(true)
```

</details>

#### BESSELK(1.5,1) matches the Excel-documented value to 6 digits

- BESSELK(1.5,1) matches the Excel-documented value to 6 digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BESSELK(1.5,1) matches the Excel-documented value to 6 digits")
expect(_approx("=BESSELK(1.5,1)", 0.277388, 0.000001)).to_be(true)
```

</details>

#### BESSELY requires x > 0 (singular at the origin)

- BESSELY requires x > 0 (singular at the origin)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BESSELY requires x > 0 (singular at the origin)")
expect(_eval("=BESSELY(0,1)")).to_contain("#ERR")
```

</details>

#### BESSELK requires x > 0

- BESSELK requires x > 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BESSELK requires x > 0")
expect(_eval("=BESSELK(-1,1)")).to_contain("#ERR")
```

</details>

#### rejects negative order

- rejects negative order


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative order")
expect(_eval("=BESSELY(2.5,-1)")).to_contain("#ERR")
```

</details>

### Calc bare ROW() / COLUMN()

#### bare ROW() resolves to the origin cell row through the recalc driver

- bare ROW() resolves to the origin cell row through the recalc driver
   - Expected: cell_display_text(sh.get_cell("C5")) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bare ROW() resolves to the origin cell row through the recalc driver")
var sh = Sheet.new("f")
sh.set_value("C5", "=ROW()")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("C5"))).to_equal("5")
```

</details>

#### bare COLUMN() resolves to the origin cell column through the recalc driver

- bare COLUMN() resolves to the origin cell column through the recalc driver
   - Expected: cell_display_text(sh.get_cell("D3")) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bare COLUMN() resolves to the origin cell column through the recalc driver")
var sh = Sheet.new("f")
sh.set_value("D3", "=COLUMN()")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("D3"))).to_equal("4")
```

</details>

#### ROW(ref) still returns the referenced row (with-arg form intact)

- ROW(ref) still returns the referenced row (with-arg form intact)
   - Expected: _eval("=ROW(B7)") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ROW(ref) still returns the referenced row (with-arg form intact)")
expect(_eval("=ROW(B7)")).to_equal("7")
```

</details>

#### bare ROW() with no cell context (direct evaluate) is #ERR

- bare ROW() with no cell context (direct evaluate) is #ERR


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bare ROW() with no cell context (direct evaluate) is #ERR")
var sh = Sheet.new("f")
val cv = evaluate_formula("=ROW()", sh)
expect(_is_error(cv)).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `2d97286940f88406a4aa49f0600108d8c9d73b99c1279e5f6e70304c6a0d5e3d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2d97286940f88406a4aa49f0600108d8c9d73b99c1279e5f6e70304c6a0d5e3d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2d97286940f88406a4aa49f0600108d8c9d73b99c1279e5f6e70304c6a0d5e3d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_card14_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_card14_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_card14_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_card14_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_card14_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the Excel documentation worked example to 6 digits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_card14_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'aliases the legacy CHITEST spelling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_card14_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'errors when the two ranges differ in size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
