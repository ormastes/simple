# formula_stat2_spec

> Calc statistical-tail distribution spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_stat2_spec

Calc statistical-tail distribution spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_stat2_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc statistical-tail distribution spec.

GAMMALN uses the Lanczos g=7 approximation (verified GAMMALN(4)=ln(6) and
GAMMALN(0.5)=ln(sqrt(pi))). WEIBULL/LOGNORMDIST/STANDARDIZE/HYPGEOMDIST/
NEGBINOMDIST are closed-form against textbook references. CONFIDENCE uses the
inverse standard normal via Acklam's rational approximation. Bad domains
(sd<=0, beta<=0, x<=0 for log/gamma) fail closed with #ERR.

## Scenarios

### Calc statistical-tail distributions

#### GAMMALN matches ln-gamma at textbook points

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- GAMMALN matches ln-gamma at textbook points


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GAMMALN matches ln-gamma at textbook points")
expect(_eval("=GAMMALN(4)")).to_start_with("1.7917594")
expect(_eval("=GAMMALN(0.5)")).to_start_with("0.5723649")
```

</details>

#### WEIBULL cumulative and density match closed forms

- WEIBULL cumulative and density match closed forms


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("WEIBULL cumulative and density match closed forms")
expect(_eval("=WEIBULL(1, 1, 1, TRUE())")).to_start_with("0.6321205")
expect(_eval("=WEIBULL(2, 2, 1, FALSE())")).to_start_with("0.0732625")
```

</details>

#### LOGNORMDIST and STANDARDIZE match references

- LOGNORMDIST and STANDARDIZE match references


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LOGNORMDIST and STANDARDIZE match references")
expect(_eval("=LOGNORMDIST(4, 3.5, 1.2)")).to_start_with("0.039083")
expect(_eval("=STANDARDIZE(42, 40, 1.5)")).to_start_with("1.3333333")
```

</details>

#### HYPGEOMDIST and NEGBINOMDIST are exact on combinatorial cases

- HYPGEOMDIST and NEGBINOMDIST are exact on combinatorial cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("HYPGEOMDIST and NEGBINOMDIST are exact on combinatorial cases")
expect(_eval("=HYPGEOMDIST(1, 4, 8, 20)")).to_start_with("0.363261")
expect(_eval("=NEGBINOMDIST(10, 5, 0.25)")).to_start_with("0.0550486")
```

</details>

#### CONFIDENCE uses the inverse normal

- CONFIDENCE uses the inverse normal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CONFIDENCE uses the inverse normal")
expect(_eval("=CONFIDENCE(0.05, 2.5, 50)")).to_start_with("0.692951")
```

</details>

#### bad domains fail closed with #ERR

- bad domains fail closed with #ERR


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bad domains fail closed with #ERR")
expect(_eval("=GAMMALN(0)")).to_contain("#ERR")
expect(_eval("=WEIBULL(1, 1, 0, TRUE())")).to_contain("#ERR")
expect(_eval("=LOGNORMDIST(4, 3.5, 0)")).to_contain("#ERR")
expect(_eval("=STANDARDIZE(42, 40, 0)")).to_contain("#ERR")
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

- Canonical SPipe generation for source `8189fe115458def2d0e54a51cbcd1a22a29c8e6830e0529712909caef859f7d3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8189fe115458def2d0e54a51cbcd1a22a29c8e6830e0529712909caef859f7d3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8189fe115458def2d0e54a51cbcd1a22a29c8e6830e0529712909caef859f7d3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_stat2_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_stat2_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_stat2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_stat2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_stat2_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'GAMMALN matches ln-gamma at textbook points' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_stat2_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'WEIBULL cumulative and density match closed forms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_stat2_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'LOGNORMDIST and STANDARDIZE match references' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
