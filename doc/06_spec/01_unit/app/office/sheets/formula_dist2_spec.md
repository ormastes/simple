# formula_dist2_spec

> Calc continuous-distribution machinery spec (CARD 2).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_dist2_spec

Calc continuous-distribution machinery spec (CARD 2).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_dist2_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc continuous-distribution machinery spec (CARD 2).

Covers BETA/GAMMA/CHISQ/T/F distributions + inverses, GAMMA, GAUSS, PHI, all
built on two primitives probed through their functions: the regularized
incomplete beta I_x(a,b) (Lentz continued fraction, NR 6.4) and the
regularized lower incomplete gamma P(a,x) (series + CF, NR 6.2). Ground truths
are Excel-documented; two of the plan card's cited values were transcription
errors and are asserted here at their true (mpmath-40-digit + closed-form
verified) values, noted inline:
  - F.INV(0.01,6,4) = 0.1093099 (plan said 0.1093861 -> cdf 0.010017, not 0.01)
  - GAMMA(-3.75)    = 0.2678661 (plan said 0.2678539; GAMMA(2.5)=1.3293404 OK)

## Scenarios

### Calc incomplete-beta primitive (via BETA/T/F/CHISQ)

#### I_x(a,b) hits hand-computed points through BETADIST/BETA.DIST

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- I_x(a,b) hits hand-computed points through BETADIST/BETA.DIST


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("I_x(a,b) hits hand-computed points through BETADIST/BETA.DIST")
expect(_eval("=BETA.DIST(0.5, 2, 3, TRUE())")).to_start_with("0.6875")
expect(_eval("=BETADIST(0.25, 2, 2)")).to_start_with("0.15625")
expect(_eval("=BETADIST(0.5, 0.5, 0.5)")).to_start_with("0.5")
```

</details>

#### incomplete gamma P(a,x) hits closed-form points

- incomplete gamma P(a,x) hits closed-form points


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("incomplete gamma P(a,x) hits closed-form points")
expect(_eval("=GAMMA.DIST(1, 1, 1, TRUE())")).to_start_with("0.632120")
expect(_eval("=CHISQ.DIST(1, 1, TRUE())")).to_start_with("0.682689")
```

</details>

### Calc BETA / GAMMA distributions

#### BETA.DIST rescales [lo,hi] and BETA.INV round-trips

- BETA.DIST rescales [lo,hi] and BETA.INV round-trips


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BETA.DIST rescales [lo,hi] and BETA.INV round-trips")
expect(_eval("=BETA.DIST(2, 8, 10, TRUE(), 1, 3)")).to_start_with("0.685470")
expect(_eval("=BETA.INV(0.6854706, 8, 10, 1, 3)")).to_start_with("2.000000")
expect(_eval("=BETAINV(0.6854706, 8, 10, 1, 3)")).to_start_with("2.000000")
```

</details>

#### GAMMA.DIST cdf and GAMMA.INV round-trip; legacy aliases match

- GAMMA.DIST cdf and GAMMA.INV round-trip; legacy aliases match


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GAMMA.DIST cdf and GAMMA.INV round-trip; legacy aliases match")
expect(_eval("=GAMMA.DIST(10.00001131, 9, 2, TRUE())")).to_start_with("0.068094")
expect(_eval("=GAMMADIST(10.00001131, 9, 2, TRUE())")).to_start_with("0.068094")
expect(_eval("=GAMMA.INV(0.068094, 9, 2)")).to_start_with("10.00001")
expect(_eval("=GAMMAINV(0.068094, 9, 2)")).to_start_with("10.00001")
```

</details>

### Calc CHI-SQUARE distribution

#### CHISQ.DIST left cdf and right-tail forms

- CHISQ.DIST left cdf and right-tail forms


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CHISQ.DIST left cdf and right-tail forms")
expect(_eval("=CHISQ.DIST(0.5, 1, TRUE())")).to_start_with("0.520499")
expect(_eval("=CHISQ.DIST.RT(18.307, 10)")).to_start_with("0.0500005")
expect(_eval("=CHIDIST(18.307, 10)")).to_start_with("0.0500005")
```

</details>

#### CHISQ.INV and right-tail inverse (legacy CHIINV)

- CHISQ.INV and right-tail inverse (legacy CHIINV)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CHISQ.INV and right-tail inverse (legacy CHIINV)")
expect(_eval("=CHISQ.INV(0.93, 1)")).to_start_with("3.283020")
expect(_eval("=CHISQ.INV.RT(0.05, 10)")).to_start_with("18.3070")
expect(_eval("=CHIINV(0.05, 1)")).to_start_with("3.841458")
```

</details>

### Calc STUDENT-T distribution

#### T.DIST cdf, 2-tailed and right-tail

- T.DIST cdf, 2-tailed and right-tail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("T.DIST cdf, 2-tailed and right-tail")
expect(_eval("=T.DIST(60, 1, TRUE())")).to_start_with("0.9946953")
expect(_eval("=T.DIST(1.96, 60, TRUE())")).to_start_with("0.972677")
expect(_eval("=T.DIST.2T(1.959999998, 60)")).to_start_with("0.0546449")
expect(_eval("=TDIST(1.959999998, 60, 2)")).to_start_with("0.0546449")
```

</details>

#### T.INV one-tail, T.INV.2T two-tail, legacy TINV (two-tail)

- T.INV one-tail, T.INV.2T two-tail, legacy TINV (two-tail)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("T.INV one-tail, T.INV.2T two-tail, legacy TINV (two-tail)")
expect(_eval("=T.INV(0.75, 2)")).to_start_with("0.816496")
expect(_eval("=T.INV.2T(0.05, 60)")).to_start_with("2.000297")
expect(_eval("=TINV(0.05, 60)")).to_start_with("2.000297")
```

</details>

### Calc F distribution

#### F.DIST cdf and right-tail (legacy FDIST)

- F.DIST cdf and right-tail (legacy FDIST)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.DIST cdf and right-tail (legacy FDIST)")
expect(_eval("=F.DIST(15.20686486, 6, 4, TRUE())")).to_start_with("0.9899999")
expect(_eval("=F.DIST.RT(15.20686486, 6, 4)")).to_start_with("0.0100000")
expect(_eval("=FDIST(15.20686486, 6, 4)")).to_start_with("0.0100000")
```

</details>

#### F.INV left inverse and right-tail inverse (legacy FINV)

- F.INV left inverse and right-tail inverse (legacy FINV)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.INV left inverse and right-tail inverse (legacy FINV)")
# plan card cited 0.1093861 (cdf 0.010017); true left inverse is 0.1093099
expect(_eval("=F.INV(0.01, 6, 4)")).to_start_with("0.109309")
expect(_eval("=F.INV.RT(0.05, 6, 4)")).to_start_with("6.163132")
expect(_eval("=FINV(0.05, 6, 4)")).to_start_with("6.163132")
```

</details>

### Calc GAMMA / GAUSS / PHI

#### GAMMA with reflection for negative non-integers

- GAMMA with reflection for negative non-integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GAMMA with reflection for negative non-integers")
expect(_eval("=GAMMA(2.5)")).to_start_with("1.329340")
# plan card cited 0.2678539; true Gamma(-3.75) is 0.2678661
expect(_eval("=GAMMA(-3.75)")).to_start_with("0.267866")
```

</details>

#### GAUSS = Phi(z)-0.5 and PHI = standard normal pdf

- GAUSS = Phi(z)-0.5 and PHI = standard normal pdf


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GAUSS = Phi(z)-0.5 and PHI = standard normal pdf")
expect(_eval("=GAUSS(2)")).to_start_with("0.477249")
expect(_eval("=PHI(0.75)")).to_start_with("0.301137")
```

</details>

### Calc dotted-name lexing and error domains

#### digit-tailed dotted names lex and mix with plain calls

- digit-tailed dotted names lex and mix with plain calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("digit-tailed dotted names lex and mix with plain calls")
# T.DIST.2T (.2T dot-then-digit) + GAMMA(1)=1 in one formula
expect(_eval("=T.DIST.2T(1.959999998, 60) + GAMMA(1)")).to_start_with("1.0546449")
```

</details>

#### domain violations fail closed with #ERR

- domain violations fail closed with #ERR


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("domain violations fail closed with #ERR")
expect(_eval("=BETA.DIST(0.5, 0, 3, TRUE())")).to_contain("#ERR")
expect(_eval("=T.DIST(1, 0.5, TRUE())")).to_contain("#ERR")
expect(_eval("=GAMMA.INV(1, 9, 2)")).to_contain("#ERR")
expect(_eval("=GAMMA(0)")).to_contain("#ERR")
expect(_eval("=GAMMA(-2)")).to_contain("#ERR")
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

- Canonical SPipe generation for source `7953d64afc1954e8415076c4cc9c6c687b03d1f4aca8848c6975656901a2cc6c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7953d64afc1954e8415076c4cc9c6c687b03d1f4aca8848c6975656901a2cc6c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7953d64afc1954e8415076c4cc9c6c687b03d1f4aca8848c6975656901a2cc6c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_dist2_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_dist2_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_dist2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_dist2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_dist2_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'I_x(a,b) hits hand-computed points through BETADIST/BETA.DIST' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_dist2_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'incomplete gamma P(a,x) hits closed-form points' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_dist2_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BETA.DIST rescales [lo,hi] and BETA.INV round-trips' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
