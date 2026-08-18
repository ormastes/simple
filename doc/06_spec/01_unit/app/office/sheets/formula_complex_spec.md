# formula_complex_spec

> Calc complex-number + clock functions spec (123 total).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_complex_spec

Calc complex-number + clock functions spec (123 total).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_complex_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc complex-number + clock functions spec (123 total).

Complex values are Excel-style text ("3+4i"); arithmetic verified against
hand-computed products/sums; IMABS on the 3-4-5 triangle. TODAY/NOW read the
runtime clock (UTC serial — local-tz offset is a recorded ceiling), asserted
structurally against the date pack.

## Scenarios

### Calc complex numbers

#### formats and parses Excel-style complex text

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=COMPLEX(3, 4)")).to_equal("3+4i")
expect(_eval("=COMPLEX(3, -4)")).to_equal("3-4i")
expect(_eval("=COMPLEX(0, 4)")).to_equal("4i")
expect(_eval("=IMREAL(\"-2-5i\")")).to_equal("-2")
expect(_eval("=IMAGINARY(\"-2-5i\")")).to_equal("-5")
```

</details>

#### computes modulus, conjugate, sum, difference, product

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=IMABS(\"3+4i\")")).to_equal("5")
expect(_eval("=IMCONJUGATE(\"3+4i\")")).to_equal("3-4i")
expect(_eval("=IMSUM(\"3+4i\", \"1-2i\")")).to_equal("4+2i")
expect(_eval("=IMSUB(\"3+4i\", \"1-2i\")")).to_equal("2+6i")
expect(_eval("=IMPRODUCT(\"1+2i\", \"3+4i\")")).to_equal("-5+10i")
```

</details>

### Calc clock functions

#### TODAY returns a serial consistent with the date pack

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val today = _eval("=TODAY()")
val year = _eval("=YEAR(TODAY())")
expect(today.to_f64() > 46000.0).to_be(true)
expect(year.to_f64() >= 2026.0).to_be(true)
```

</details>

#### NOW is TODAY plus a day fraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diff = _eval("=NOW() - TODAY()")
expect(diff.to_f64() >= 0.0).to_be(true)
expect(diff.to_f64() < 1.0).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
