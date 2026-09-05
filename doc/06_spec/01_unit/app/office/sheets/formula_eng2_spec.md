# formula_eng2_spec

> Calc engineering-remainder spec — ERF/ERFC, IM* complex tail, Bessel, CONVERT.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_eng2_spec

Calc engineering-remainder spec — ERF/ERFC, IM* complex tail, Bessel, CONVERT.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_eng2_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc engineering-remainder spec — ERF/ERFC, IM* complex tail, Bessel, CONVERT.

Ground truths are Excel-documented. ERF is the Abramowitz-Stegun A-S 7.1.26
kernel now factored out of _norm_cdf, so a regression assertion pins
NORMSDIST(1.96)=0.97500… unchanged. Complex results are Excel-style text
("8+i", unit coefficient omitted); irrational parts are checked numerically by
extracting them back through IMREAL/IMAGINARY with a tolerance. Bessel is
series-only with a documented |x|<=15 domain (over it -> #ERR). CONVERT does
factor ratios for linear categories and affine Kelvin routing for temperature;
category mismatch -> #ERR.

## Scenarios

### Calc ERF/ERFC

#### keeps NORMSDIST identical after the _erf refactor (regression pin)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps NORMSDIST identical after the _erf refactor (regression pin)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps NORMSDIST identical after the _erf refactor (regression pin)")
expect(_eval("=NORMSDIST(1.96)")).to_start_with("0.975")
```

</details>

#### computes ERF, ERFC and the two-argument ERF

- computes ERF, ERFC and the two-argument ERF


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes ERF, ERFC and the two-argument ERF")
expect(_approx("=ERF(1)", 0.8427007, 0.00001)).to_be(true)
expect(_approx("=ERFC(1)", 0.1572992, 0.00001)).to_be(true)
expect(_approx("=ERF(0.5, 1)", 0.3222009, 0.00001)).to_be(true)
```

</details>

#### aliases ERF.PRECISE / ERFC.PRECISE to ERF / ERFC

- aliases ERF.PRECISE / ERFC.PRECISE to ERF / ERFC


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aliases ERF.PRECISE / ERFC.PRECISE to ERF / ERFC")
expect(_approx("=ERF.PRECISE(1)", 0.8427007, 0.00001)).to_be(true)
expect(_approx("=ERFC.PRECISE(1)", 0.1572992, 0.00001)).to_be(true)
```

</details>

### Calc complex IM* tail

#### arithmetic: sum omits unit coefficient, product, sub, div

- arithmetic: sum omits unit coefficient, product, sub, div
   - Expected: _eval("=IMSUM(\"3+4i\", \"5-3i\")") equals `8+i`
   - Expected: _eval("=IMPRODUCT(\"3+4i\", \"5-3i\")") equals `27+11i`
   - Expected: _eval("=IMSUB(\"3+4i\", \"5-3i\")") equals `-2+7i`
   - Expected: _eval("=IMDIV(\"-238+240i\", \"10+24i\")") equals `5+12i`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arithmetic: sum omits unit coefficient, product, sub, div")
expect(_eval("=IMSUM(\"3+4i\", \"5-3i\")")).to_equal("8+i")
expect(_eval("=IMPRODUCT(\"3+4i\", \"5-3i\")")).to_equal("27+11i")
expect(_eval("=IMSUB(\"3+4i\", \"5-3i\")")).to_equal("-2+7i")
expect(_eval("=IMDIV(\"-238+240i\", \"10+24i\")")).to_equal("5+12i")
```

</details>

#### integer power is exact via repeated multiplication

- integer power is exact via repeated multiplication
   - Expected: _eval("=IMPOWER(\"2+3i\", 3)") equals `-46+9i`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integer power is exact via repeated multiplication")
expect(_eval("=IMPOWER(\"2+3i\", 3)")).to_equal("-46+9i")
```

</details>

#### conjugate and argument

- conjugate and argument
   - Expected: _eval("=IMCONJUGATE(\"3+4i\")") equals `3-4i`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("conjugate and argument")
expect(_eval("=IMCONJUGATE(\"3+4i\")")).to_equal("3-4i")
expect(_approx("=IMARGUMENT(\"3+4i\")", 0.9272952, 0.00001)).to_be(true)
```

</details>

#### sqrt via closed form (both parts)

- sqrt via closed form (both parts)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sqrt via closed form (both parts)")
expect(_approx("=IMREAL(IMSQRT(\"1+i\"))", 1.0986841, 0.000001)).to_be(true)
expect(_approx("=IMAGINARY(IMSQRT(\"1+i\"))", 0.4550899, 0.000001)).to_be(true)
```

</details>

#### exp, ln, log10 via exp/ln/atan2

- exp, ln, log10 via exp/ln/atan2


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exp, ln, log10 via exp/ln/atan2")
expect(_approx("=IMREAL(IMEXP(\"1+i\"))", 1.4686939, 0.00001)).to_be(true)
expect(_approx("=IMAGINARY(IMEXP(\"1+i\"))", 2.2873553, 0.00001)).to_be(true)
expect(_approx("=IMREAL(IMLN(\"3+4i\"))", 1.6094379, 0.00001)).to_be(true)
expect(_approx("=IMAGINARY(IMLN(\"3+4i\"))", 0.9272952, 0.00001)).to_be(true)
expect(_approx("=IMREAL(IMLOG10(\"3+4i\"))", 0.69897, 0.00001)).to_be(true)
```

</details>

#### trigonometric sin (real cosh, imag sinh)

- trigonometric sin (real cosh, imag sinh)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trigonometric sin (real cosh, imag sinh)")
expect(_approx("=IMREAL(IMSIN(\"3+4i\"))", 3.8537380, 0.0001)).to_be(true)
expect(_approx("=IMAGINARY(IMSIN(\"3+4i\"))", -27.0168133, 0.0001)).to_be(true)
```

</details>

### Calc Bessel (series, |x|<=15)

#### BESSELJ and BESSELI integer order

- BESSELJ and BESSELI integer order


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BESSELJ and BESSELI integer order")
expect(_approx("=BESSELJ(1.9, 2)", 0.3299257, 0.000001)).to_be(true)
expect(_approx("=BESSELI(1.5, 1)", 0.9816664, 0.000001)).to_be(true)
```

</details>

#### domain ceiling and negative order are #ERR

- domain ceiling and negative order are #ERR


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("domain ceiling and negative order are #ERR")
expect(_eval("=BESSELJ(20, 2)")).to_start_with("#ERR")
expect(_eval("=BESSELJ(1.9, -1)")).to_start_with("#ERR")
```

</details>

### Calc CONVERT

#### linear categories convert by SI factor ratio

- linear categories convert by SI factor ratio


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("linear categories convert by SI factor ratio")
expect(_approx("=CONVERT(1, \"lbm\", \"kg\")", 0.4535924, 0.000001)).to_be(true)
expect(_approx("=CONVERT(1, \"mi\", \"km\")", 1.609344, 0.000001)).to_be(true)
```

</details>

#### temperature converts affinely through Kelvin

- temperature converts affinely through Kelvin


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("temperature converts affinely through Kelvin")
expect(_approx("=CONVERT(68, \"F\", \"C\")", 20.0, 0.000001)).to_be(true)
expect(_approx("=CONVERT(100, \"C\", \"F\")", 212.0, 0.000001)).to_be(true)
```

</details>

#### category mismatch and unknown units are #ERR

- category mismatch and unknown units are #ERR


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("category mismatch and unknown units are #ERR")
expect(_eval("=CONVERT(2.5, \"ft\", \"sec\")")).to_start_with("#ERR")
expect(_eval("=CONVERT(1, \"zzz\", \"kg\")")).to_start_with("#ERR")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `a18ff6c55724528affc1df8f1ff1564d4041d8ae4fd3f80632c99a1b950002af`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a18ff6c55724528affc1df8f1ff1564d4041d8ae4fd3f80632c99a1b950002af`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a18ff6c55724528affc1df8f1ff1564d4041d8ae4fd3f80632c99a1b950002af`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_eng2_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_eng2_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_eng2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_eng2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_eng2_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps NORMSDIST identical after the _erf refactor (regression pin)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_eng2_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes ERF, ERFC and the two-argument ERF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_eng2_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'aliases ERF.PRECISE / ERFC.PRECISE to ERF / ERFC' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
