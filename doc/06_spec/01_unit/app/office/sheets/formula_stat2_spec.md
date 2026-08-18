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
| Updated | 2026-08-18 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=GAMMALN(4)")).to_start_with("1.7917594")
expect(_eval("=GAMMALN(0.5)")).to_start_with("0.5723649")
```

</details>

#### WEIBULL cumulative and density match closed forms

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=WEIBULL(1, 1, 1, TRUE())")).to_start_with("0.6321205")
expect(_eval("=WEIBULL(2, 2, 1, FALSE())")).to_start_with("0.0732625")
```

</details>

#### LOGNORMDIST and STANDARDIZE match references

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LOGNORMDIST(4, 3.5, 1.2)")).to_start_with("0.039083")
expect(_eval("=STANDARDIZE(42, 40, 1.5)")).to_start_with("1.3333333")
```

</details>

#### HYPGEOMDIST and NEGBINOMDIST are exact on combinatorial cases

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=HYPGEOMDIST(1, 4, 8, 20)")).to_start_with("0.363261")
expect(_eval("=NEGBINOMDIST(10, 5, 0.25)")).to_start_with("0.0550486")
```

</details>

#### CONFIDENCE uses the inverse normal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=CONFIDENCE(0.05, 2.5, 50)")).to_start_with("0.692951")
```

</details>

#### bad domains fail closed with #ERR

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
