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
| Updated | 2026-08-18 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=NORMSDIST(1.96)")).to_start_with("0.975")
```

</details>

#### computes ERF, ERFC and the two-argument ERF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_approx("=ERF(1)", 0.8427007, 0.00001)).to_be(true)
expect(_approx("=ERFC(1)", 0.1572992, 0.00001)).to_be(true)
expect(_approx("=ERF(0.5, 1)", 0.3222009, 0.00001)).to_be(true)
```

</details>

#### aliases ERF.PRECISE / ERFC.PRECISE to ERF / ERFC

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_approx("=ERF.PRECISE(1)", 0.8427007, 0.00001)).to_be(true)
expect(_approx("=ERFC.PRECISE(1)", 0.1572992, 0.00001)).to_be(true)
```

</details>

### Calc complex IM* tail

#### arithmetic: sum omits unit coefficient, product, sub, div

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=IMSUM(\"3+4i\", \"5-3i\")")).to_equal("8+i")
expect(_eval("=IMPRODUCT(\"3+4i\", \"5-3i\")")).to_equal("27+11i")
expect(_eval("=IMSUB(\"3+4i\", \"5-3i\")")).to_equal("-2+7i")
expect(_eval("=IMDIV(\"-238+240i\", \"10+24i\")")).to_equal("5+12i")
```

</details>

#### integer power is exact via repeated multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=IMPOWER(\"2+3i\", 3)")).to_equal("-46+9i")
```

</details>

#### conjugate and argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=IMCONJUGATE(\"3+4i\")")).to_equal("3-4i")
expect(_approx("=IMARGUMENT(\"3+4i\")", 0.9272952, 0.00001)).to_be(true)
```

</details>

#### sqrt via closed form (both parts)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_approx("=IMREAL(IMSQRT(\"1+i\"))", 1.0986841, 0.000001)).to_be(true)
expect(_approx("=IMAGINARY(IMSQRT(\"1+i\"))", 0.4550899, 0.000001)).to_be(true)
```

</details>

#### exp, ln, log10 via exp/ln/atan2

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_approx("=IMREAL(IMEXP(\"1+i\"))", 1.4686939, 0.00001)).to_be(true)
expect(_approx("=IMAGINARY(IMEXP(\"1+i\"))", 2.2873553, 0.00001)).to_be(true)
expect(_approx("=IMREAL(IMLN(\"3+4i\"))", 1.6094379, 0.00001)).to_be(true)
expect(_approx("=IMAGINARY(IMLN(\"3+4i\"))", 0.9272952, 0.00001)).to_be(true)
expect(_approx("=IMREAL(IMLOG10(\"3+4i\"))", 0.69897, 0.00001)).to_be(true)
```

</details>

#### trigonometric sin (real cosh, imag sinh)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_approx("=IMREAL(IMSIN(\"3+4i\"))", 3.8537380, 0.0001)).to_be(true)
expect(_approx("=IMAGINARY(IMSIN(\"3+4i\"))", -27.0168133, 0.0001)).to_be(true)
```

</details>

### Calc Bessel (series, |x|<=15)

#### BESSELJ and BESSELI integer order

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_approx("=BESSELJ(1.9, 2)", 0.3299257, 0.000001)).to_be(true)
expect(_approx("=BESSELI(1.5, 1)", 0.9816664, 0.000001)).to_be(true)
```

</details>

#### domain ceiling and negative order are #ERR

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=BESSELJ(20, 2)")).to_start_with("#ERR")
expect(_eval("=BESSELJ(1.9, -1)")).to_start_with("#ERR")
```

</details>

### Calc CONVERT

#### linear categories convert by SI factor ratio

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_approx("=CONVERT(1, \"lbm\", \"kg\")", 0.4535924, 0.000001)).to_be(true)
expect(_approx("=CONVERT(1, \"mi\", \"km\")", 1.609344, 0.000001)).to_be(true)
```

</details>

#### temperature converts affinely through Kelvin

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_approx("=CONVERT(68, \"F\", \"C\")", 20.0, 0.000001)).to_be(true)
expect(_approx("=CONVERT(100, \"C\", \"F\")", 212.0, 0.000001)).to_be(true)
```

</details>

#### category mismatch and unknown units are #ERR

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
