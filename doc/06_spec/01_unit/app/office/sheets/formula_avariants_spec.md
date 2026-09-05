# formula_avariants_spec

> Calc stat A-variants + EXC percentiles + CRITBINOM + array remainder spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_avariants_spec

Calc stat A-variants + EXC percentiles + CRITBINOM + array remainder spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_avariants_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc stat A-variants + EXC percentiles + CRITBINOM + array remainder spec.

The *A statistics (AVERAGEA/MAXA/MINA/STDEVA/VARA/STDEVPA/VARPA) read raw typed
cells: text counts as 0, TRUE=1/FALSE=0, empty cells are skipped. Ground truth
for cells [10, "x", TRUE, 20] is the value set {10, 0, 1, 20}: AVERAGEA=31/4=7.75,
MAXA=20, MINA=0, sample VARA=Sum((x-7.75)^2)/3=260.75/3=86.916666..,
STDEVA=sqrt(86.916666)=9.322910.., population VARPA=260.75/4=65.1875,
STDEVPA=sqrt(65.1875)=8.073877.. (all hand-verified).

Exclusive percentiles use position = p*(n+1), 1-based, #ERR when the position
falls outside [1, n]: PERCENTILE.EXC([1,2,3,4],0.4)=2 (pos 2.0);
QUARTILE.EXC of the 11-value Excel-documented set at q=1 = 15 (pos 3.0);
PERCENTRANK.EXC([1,2,3,4],2)=2/(4+1)=0.4. CRITBINOM(6,0.5,0.75)=4 (first k with
binomial CDF>=0.75: CDF(3)=0.65625, CDF(4)=0.890625).

Array-returning functions spill a 2D grid: MODE.MULT (all repeated values, first
seen order, down one column), SORTBY, WRAPROWS, WRAPCOLS, EXPAND.

## Scenarios

### Calc stat A-variants — text=0, bool=1/0, empty skipped

#### AVERAGEA averages {10,0,1,20} = 7.75 (text is 0, TRUE is 1)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AVERAGEA averages {10,0,1,20} = 7.75 (text is 0, TRUE is 1)
   - Expected: _eval("=AVERAGEA(A1:A4)") equals `7.75`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AVERAGEA averages {10,0,1,20} = 7.75 (text is 0, TRUE is 1)")
expect(_eval("=AVERAGEA(A1:A4)")).to_equal("7.75")
```

</details>

#### MAXA of {10,0,1,20} is 20

- MAXA of {10,0,1,20} is 20
   - Expected: _eval("=MAXA(A1:A4)") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MAXA of {10,0,1,20} is 20")
expect(_eval("=MAXA(A1:A4)")).to_equal("20")
```

</details>

#### MINA of {10,0,1,20} is 0 (text counts as 0)

- MINA of {10,0,1,20} is 0 (text counts as 0)
   - Expected: _eval("=MINA(A1:A4)") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MINA of {10,0,1,20} is 0 (text counts as 0)")
expect(_eval("=MINA(A1:A4)")).to_equal("0")
```

</details>

#### VARA sample variance of {10,0,1,20} is 86.9166..

- VARA sample variance of {10,0,1,20} is 86.9166..


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VARA sample variance of {10,0,1,20} is 86.9166..")
expect(_eval("=VARA(A1:A4)")).to_start_with("86.9166")
```

</details>

#### STDEVA is sqrt of VARA = 9.3229..

- STDEVA is sqrt of VARA = 9.3229..


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("STDEVA is sqrt of VARA = 9.3229..")
expect(_eval("=STDEVA(A1:A4)")).to_start_with("9.3229")
```

</details>

#### VARPA population variance of {10,0,1,20} is 65.1875

- VARPA population variance of {10,0,1,20} is 65.1875
   - Expected: _eval("=VARPA(A1:A4)") equals `65.1875`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VARPA population variance of {10,0,1,20} is 65.1875")
expect(_eval("=VARPA(A1:A4)")).to_equal("65.1875")
```

</details>

#### STDEVPA is sqrt of VARPA = 8.0738..

- STDEVPA is sqrt of VARPA = 8.0738..


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("STDEVPA is sqrt of VARPA = 8.0738..")
expect(_eval("=STDEVPA(A1:A4)")).to_start_with("8.0738")
```

</details>

#### AVERAGEA skips the blank A5, still 7.75

- AVERAGEA skips the blank A5, still 7.75
   - Expected: _eval("=AVERAGEA(A1:A5)") equals `7.75`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AVERAGEA skips the blank A5, still 7.75")
expect(_eval("=AVERAGEA(A1:A5)")).to_equal("7.75")
```

</details>

#### VARA needs 2+ values, fails closed on a single cell

- VARA needs 2+ values, fails closed on a single cell


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VARA needs 2+ values, fails closed on a single cell")
expect(_eval("=VARA(A1:A1)")).to_contain("#ERR")
```

</details>

### Calc exclusive percentiles — position p*(n+1)

#### PERCENTILE.EXC([1,2,3,4],0.4) lands exactly on the 2nd value = 2

- PERCENTILE.EXC([1,2,3,4],0.4) lands exactly on the 2nd value = 2
   - Expected: _eval("=PERCENTILE.EXC(B1:B4,0.4)") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PERCENTILE.EXC([1,2,3,4],0.4) lands exactly on the 2nd value = 2")
expect(_eval("=PERCENTILE.EXC(B1:B4,0.4)")).to_equal("2")
```

</details>

#### QUARTILE.EXC of the documented 11-value set at q=1 = 15

- QUARTILE.EXC of the documented 11-value set at q=1 = 15
   - Expected: _eval("=QUARTILE.EXC(C1:C11,1)") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("QUARTILE.EXC of the documented 11-value set at q=1 = 15")
expect(_eval("=QUARTILE.EXC(C1:C11,1)")).to_equal("15")
```

</details>

#### PERCENTRANK.EXC([1,2,3,4],2) = 2/(4+1) = 0.4

- PERCENTRANK.EXC([1,2,3,4],2) = 2/(4+1) = 0.4


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PERCENTRANK.EXC([1,2,3,4],2) = 2/(4+1) = 0.4")
expect(_eval("=PERCENTRANK.EXC(B1:B4,2)")).to_start_with("0.4")
```

</details>

#### PERCENTILE.EXC rejects k<=0 as a domain error

- PERCENTILE.EXC rejects k<=0 as a domain error


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PERCENTILE.EXC rejects k<=0 as a domain error")
expect(_eval("=PERCENTILE.EXC(B1:B4,0)")).to_contain("#ERR")
```

</details>

#### QUARTILE.EXC rejects q=4 (position n+1 is out of range)

- QUARTILE.EXC rejects q=4 (position n+1 is out of range)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("QUARTILE.EXC rejects q=4 (position n+1 is out of range)")
expect(_eval("=QUARTILE.EXC(B1:B4,4)")).to_contain("#ERR")
```

</details>

#### PERCENTRANK.EXC rejects a value below the minimum

- PERCENTRANK.EXC rejects a value below the minimum


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PERCENTRANK.EXC rejects a value below the minimum")
expect(_eval("=PERCENTRANK.EXC(B1:B4,0)")).to_contain("#ERR")
```

</details>

### Calc CRITBINOM — smallest k with CDF >= alpha

#### CRITBINOM(6,0.5,0.75) = 4

- CRITBINOM(6,0.5,0.75) = 4
   - Expected: _eval("=CRITBINOM(6,0.5,0.75)") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CRITBINOM(6,0.5,0.75) = 4")
expect(_eval("=CRITBINOM(6,0.5,0.75)")).to_equal("4")
```

</details>

#### CRITBINOM rejects a probability above 1

- CRITBINOM rejects a probability above 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CRITBINOM rejects a probability above 1")
expect(_eval("=CRITBINOM(6,1.5,0.75)")).to_contain("#ERR")
```

</details>

### Calc MODE.MULT — all modes spilled down a column

#### MODE.MULT of [1,2,2,3,3,4] spills [2,3] in first-seen order

- MODE.MULT of [1,2,2,3,3,4] spills [2,3] in first-seen order
   - Expected: _disp(sh, "A1") equals `2`
   - Expected: _disp(sh, "A2") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MODE.MULT of [1,2,2,3,3,4] spills [2,3] in first-seen order")
var sh = Sheet.new("m")
sh.set_value("H1", "1")
sh.set_value("H2", "2")
sh.set_value("H3", "2")
sh.set_value("H4", "3")
sh.set_value("H5", "3")
sh.set_value("H6", "4")
sh.set_value("A1", "=MODE.MULT(H1:H6)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("2")
expect(_disp(sh, "A2")).to_equal("3")
```

</details>

#### MODE.MULT fails closed with #ERR when nothing repeats

- MODE.MULT fails closed with #ERR when nothing repeats
   - Expected: _disp(sh, "A1") equals `#ERR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MODE.MULT fails closed with #ERR when nothing repeats")
var sh = Sheet.new("m")
sh.set_value("H1", "1")
sh.set_value("H2", "2")
sh.set_value("H3", "3")
sh.set_value("A1", "=MODE.MULT(H1:H3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("#ERR")
```

</details>

### Calc SORTBY — rows reordered by a parallel key column

#### SORTBY([a,b,c] by [3,1,2]) ascending spills [b,c,a]

- SORTBY([a,b,c] by [3,1,2]) ascending spills [b,c,a]
   - Expected: _disp(sh, "A1") equals `b`
   - Expected: _disp(sh, "A2") equals `c`
   - Expected: _disp(sh, "A3") equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SORTBY([a,b,c] by [3,1,2]) ascending spills [b,c,a]")
var sh = Sheet.new("sb")
sh.set_value("H1", "a")
sh.set_value("H2", "b")
sh.set_value("H3", "c")
sh.set_value("I1", "3")
sh.set_value("I2", "1")
sh.set_value("I3", "2")
sh.set_value("A1", "=SORTBY(H1:H3,I1:I3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("b")
expect(_disp(sh, "A2")).to_equal("c")
expect(_disp(sh, "A3")).to_equal("a")
```

</details>

### Calc WRAPROWS / WRAPCOLS — wrap a vector into a grid

#### WRAPROWS([1..5],2) fills rows of 2, padding the last with #N/A

- WRAPROWS([1..5],2) fills rows of 2, padding the last with #N/A
   - Expected: _disp(sh, "A1") equals `1`
   - Expected: _disp(sh, "B1") equals `2`
   - Expected: _disp(sh, "A2") equals `3`
   - Expected: _disp(sh, "B2") equals `4`
   - Expected: _disp(sh, "A3") equals `5`
   - Expected: _disp(sh, "B3") equals `#N/A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("WRAPROWS([1..5],2) fills rows of 2, padding the last with #N/A")
var sh = Sheet.new("wr")
sh.set_value("H1", "1")
sh.set_value("H2", "2")
sh.set_value("H3", "3")
sh.set_value("H4", "4")
sh.set_value("H5", "5")
sh.set_value("A1", "=WRAPROWS(H1:H5,2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "B1")).to_equal("2")
expect(_disp(sh, "A2")).to_equal("3")
expect(_disp(sh, "B2")).to_equal("4")
expect(_disp(sh, "A3")).to_equal("5")
expect(_disp(sh, "B3")).to_equal("#N/A")
```

</details>

#### WRAPCOLS([1..5],2) fills columns of 2, padding the last with #N/A

- WRAPCOLS([1..5],2) fills columns of 2, padding the last with #N/A
   - Expected: _disp(sh, "A1") equals `1`
   - Expected: _disp(sh, "B1") equals `3`
   - Expected: _disp(sh, "C1") equals `5`
   - Expected: _disp(sh, "A2") equals `2`
   - Expected: _disp(sh, "B2") equals `4`
   - Expected: _disp(sh, "C2") equals `#N/A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("WRAPCOLS([1..5],2) fills columns of 2, padding the last with #N/A")
var sh = Sheet.new("wc")
sh.set_value("H1", "1")
sh.set_value("H2", "2")
sh.set_value("H3", "3")
sh.set_value("H4", "4")
sh.set_value("H5", "5")
sh.set_value("A1", "=WRAPCOLS(H1:H5,2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "B1")).to_equal("3")
expect(_disp(sh, "C1")).to_equal("5")
expect(_disp(sh, "A2")).to_equal("2")
expect(_disp(sh, "B2")).to_equal("4")
expect(_disp(sh, "C2")).to_equal("#N/A")
```

</details>

### Calc EXPAND — grow a grid, padding new cells

#### EXPAND of a 1x2 range to 2x3 pads new cells with #N/A

- EXPAND of a 1x2 range to 2x3 pads new cells with #N/A
   - Expected: _disp(sh, "A1") equals `a`
   - Expected: _disp(sh, "B1") equals `b`
   - Expected: _disp(sh, "C1") equals `#N/A`
   - Expected: _disp(sh, "A2") equals `#N/A`
   - Expected: _disp(sh, "B2") equals `#N/A`
   - Expected: _disp(sh, "C2") equals `#N/A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EXPAND of a 1x2 range to 2x3 pads new cells with #N/A")
var sh = Sheet.new("ex")
sh.set_value("H1", "a")
sh.set_value("I1", "b")
sh.set_value("A1", "=EXPAND(H1:I1,2,3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("a")
expect(_disp(sh, "B1")).to_equal("b")
expect(_disp(sh, "C1")).to_equal("#N/A")
expect(_disp(sh, "A2")).to_equal("#N/A")
expect(_disp(sh, "B2")).to_equal("#N/A")
expect(_disp(sh, "C2")).to_equal("#N/A")
```

</details>

#### EXPAND fails closed with #ERR when shrinking below the source

- EXPAND fails closed with #ERR when shrinking below the source
   - Expected: _disp(sh, "A1") equals `#ERR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EXPAND fails closed with #ERR when shrinking below the source")
var sh = Sheet.new("ex")
sh.set_value("H1", "a")
sh.set_value("I1", "b")
sh.set_value("A1", "=EXPAND(H1:I1,1,1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("#ERR")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
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

- Canonical SPipe generation for source `633d8369ffaf0afeb8af6e085f020f7672fde574eb5f89d1427b3ccdd980eb8e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `633d8369ffaf0afeb8af6e085f020f7672fde574eb5f89d1427b3ccdd980eb8e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `633d8369ffaf0afeb8af6e085f020f7672fde574eb5f89d1427b3ccdd980eb8e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_avariants_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_avariants_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_avariants_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_avariants_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_avariants_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AVERAGEA averages {10,0,1,20} = 7.75 (text is 0, TRUE is 1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_avariants_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'MAXA of {10,0,1,20} is 20' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_avariants_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'MINA of {10,0,1,20} is 0 (text counts as 0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
