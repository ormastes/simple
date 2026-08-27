# Distributions Specification

> Tests covering std.math.distributions (normal), std.math.distributions (Student's t), std.math.distributions (chi-squared), std.math.distributions (F distribution), std.math.distributions (beta), std.math.distributions (gamma), std.math.distributions (binomial), std.math.distributions (Poisson), std.math.distributions (exponential), std.math.distributions (hypergeometric), std.math.distributions (negative binomial), std.math.distributions (Weibull), std.math.distributions (log-normal).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 55 | 55 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Distributions Specification

## Scenarios

### std.math.distributions (normal)

#### norm_pdf

#### norm_pdf(0,0,1) is 1/sqrt(2*pi) ~ 0.398942

- norm_pdf(0,0,1) is 1/sqrt(2*pi) ~ 0.398942


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("norm_pdf(0,0,1) is 1/sqrt(2*pi) ~ 0.398942")
val res = norm_pdf(0.0, 0.0, 1.0)
expect(_approx(res, 0.3989422804, 0.0001)).to_be(true)
```

</details>

#### norm_pdf domain error (sd<=0) is NaN

- norm_pdf domain error (sd<=0) is NaN


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("norm_pdf domain error (sd<=0) is NaN")
val res = norm_pdf(0.0, 0.0, 0.0)
expect(_is_nan(res)).to_be(true)
```

</details>

#### norm_cdf

#### norm_cdf(1.96,0,1) is 0.9750021

- norm_cdf(1.96,0,1) is 0.9750021


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("norm_cdf(1.96,0,1) is 0.9750021")
val res = norm_cdf(1.96, 0.0, 1.0)
expect(_approx(res, 0.9750021, 0.0001)).to_be(true)
```

</details>

#### norm_cdf(0,0,1) is 0.5 (median)

- norm_cdf(0,0,1) is 0.5 (median)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("norm_cdf(0,0,1) is 0.5 (median)")
val res = norm_cdf(0.0, 0.0, 1.0)
expect(_approx(res, 0.5, 0.0001)).to_be(true)
```

</details>

#### norm_inv

#### norm_inv(0.975,0,1) is 1.959964

- norm_inv(0.975,0,1) is 1.959964


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("norm_inv(0.975,0,1) is 1.959964")
val res = norm_inv(0.975, 0.0, 1.0)
expect(_approx(res, 1.959964, 0.0001)).to_be(true)
```

</details>

#### round-trip: norm_inv(norm_cdf(0.5)) ~= 0.5

- round-trip: norm_inv(norm_cdf(0.5)) ~= 0.5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip: norm_inv(norm_cdf(0.5)) ~= 0.5")
val res = norm_inv(norm_cdf(0.5, 0.0, 1.0), 0.0, 1.0)
expect(_approx(res, 0.5, 0.00001)).to_be(true)
```

</details>

#### round-trip: norm_inv(norm_cdf(-1.2)) ~= -1.2

- round-trip: norm_inv(norm_cdf(-1.2)) ~= -1.2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip: norm_inv(norm_cdf(-1.2)) ~= -1.2")
val res = norm_inv(norm_cdf(-1.2, 0.0, 1.0), 0.0, 1.0)
expect(_approx(res, -1.2, 0.00001)).to_be(true)
```

</details>

#### norm_inv domain error (p out of (0,1)) is NaN

- norm_inv domain error (p out of (0,1)) is NaN


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("norm_inv domain error (p out of (0,1)) is NaN")
val res = norm_inv(1.5, 0.0, 1.0)
expect(_is_nan(res)).to_be(true)
```

</details>

### std.math.distributions (Student's t)

#### t_cdf

#### t_cdf(0,10) is 0.5 (median)

- t_cdf(0,10) is 0.5 (median)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t_cdf(0,10) is 0.5 (median)")
val res = t_cdf(0.0, 10.0)
expect(_approx(res, 0.5, 0.0001)).to_be(true)
```

</details>

#### t_cdf_2t(2.228139,10) is ~0.05 (two-tailed 5%)

- t_cdf_2t(2.228139,10) is ~0.05 (two-tailed 5%)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t_cdf_2t(2.228139,10) is ~0.05 (two-tailed 5%)")
val res = t_cdf_2t(2.228139, 10.0)
expect(_approx(res, 0.05, 0.0001)).to_be(true)
```

</details>

#### t_inv

#### t_inv(0.975,10) is 2.228139

- t_inv(0.975,10) is 2.228139


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t_inv(0.975,10) is 2.228139")
val res = t_inv(0.975, 10.0)
expect(_approx(res, 2.228139, 0.0001)).to_be(true)
```

</details>

#### t_inv(0.5,10) is 0 (median)

- t_inv(0.5,10) is 0 (median)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t_inv(0.5,10) is 0 (median)")
val res = t_inv(0.5, 10.0)
expect(_approx(res, 0.0, 0.0001)).to_be(true)
```

</details>

#### round-trip: t_inv(t_cdf(1.5,df=7)) ~= 1.5

- round-trip: t_inv(t_cdf(1.5,df=7)) ~= 1.5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip: t_inv(t_cdf(1.5,df=7)) ~= 1.5")
val res = t_inv(t_cdf(1.5, 7.0), 7.0)
expect(_approx(res, 1.5, 0.00001)).to_be(true)
```

</details>

#### round-trip: t_inv(t_cdf(-0.8,df=20)) ~= -0.8

- round-trip: t_inv(t_cdf(-0.8,df=20)) ~= -0.8


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip: t_inv(t_cdf(-0.8,df=20)) ~= -0.8")
val res = t_inv(t_cdf(-0.8, 20.0), 20.0)
expect(_approx(res, -0.8, 0.00001)).to_be(true)
```

</details>

#### t_inv domain error (df<1) is NaN

- t_inv domain error (df<1) is NaN


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t_inv domain error (df<1) is NaN")
val res = t_inv(0.5, 0.5)
expect(_is_nan(res)).to_be(true)
```

</details>

### std.math.distributions (chi-squared)

#### chisq_cdf/chisq_inv

#### chisq_inv(0.95,5) is 11.0705

- chisq_inv(0.95,5) is 11.0705


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chisq_inv(0.95,5) is 11.0705")
val res = chisq_inv(0.95, 5.0)
expect(_approx(res, 11.0705, 0.001)).to_be(true)
```

</details>

#### round-trip: chisq_inv(chisq_cdf(5.0,df=4)) ~= 5.0

- round-trip: chisq_inv(chisq_cdf(5.0,df=4)) ~= 5.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip: chisq_inv(chisq_cdf(5.0,df=4)) ~= 5.0")
val res = chisq_inv(chisq_cdf(5.0, 4.0), 4.0)
expect(_approx(res, 5.0, 0.00001)).to_be(true)
```

</details>

#### round-trip: chisq_inv(chisq_cdf(12.0,df=9)) ~= 12.0

- round-trip: chisq_inv(chisq_cdf(12.0,df=9)) ~= 12.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip: chisq_inv(chisq_cdf(12.0,df=9)) ~= 12.0")
val res = chisq_inv(chisq_cdf(12.0, 9.0), 9.0)
expect(_approx(res, 12.0, 0.00001)).to_be(true)
```

</details>

#### chisq_cdf domain error (x<0) is NaN

- chisq_cdf domain error (x<0) is NaN


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chisq_cdf domain error (x<0) is NaN")
val res = chisq_cdf(-1.0, 5.0)
expect(_is_nan(res)).to_be(true)
```

</details>

### std.math.distributions (F distribution)

#### f_cdf/f_inv

#### f_cdf(3.0,5,10) is 0.934442 (via incomplete beta I_{d1*x/(d1*x+d2)}(d1/2,d2/2))

- f_cdf(3.0,5,10) is 0.934442 (via incomplete beta I_{d1*x/(d1*x+d2)}(d1/2,d2/2))


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("f_cdf(3.0,5,10) is 0.934442 (via incomplete beta I_{d1*x/(d1*x+d2)}(d1/2,d2/2))")
val res = f_cdf(3.0, 5.0, 10.0)
expect(_approx(res, 0.934442, 0.000001)).to_be(true)
```

</details>

#### round-trip: f_inv(f_cdf(2.0,d1=4,d2=8)) ~= 2.0

- round-trip: f_inv(f_cdf(2.0,d1=4,d2=8)) ~= 2.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip: f_inv(f_cdf(2.0,d1=4,d2=8)) ~= 2.0")
val res = f_inv(f_cdf(2.0, 4.0, 8.0), 4.0, 8.0)
expect(_approx(res, 2.0, 0.00001)).to_be(true)
```

</details>

#### round-trip: f_inv(f_cdf(1.5,d1=6,d2=12)) ~= 1.5

- round-trip: f_inv(f_cdf(1.5,d1=6,d2=12)) ~= 1.5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip: f_inv(f_cdf(1.5,d1=6,d2=12)) ~= 1.5")
val res = f_inv(f_cdf(1.5, 6.0, 12.0), 6.0, 12.0)
expect(_approx(res, 1.5, 0.00001)).to_be(true)
```

</details>

#### f_cdf domain error (d1<1) is NaN

- f_cdf domain error (d1<1) is NaN


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("f_cdf domain error (d1<1) is NaN")
val res = f_cdf(1.0, 0.5, 10.0)
expect(_is_nan(res)).to_be(true)
```

</details>

### std.math.distributions (beta)

#### beta_cdf/beta_inv

#### beta_cdf(0.4,2,3) is 0.5248

- beta_cdf(0.4,2,3) is 0.5248


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("beta_cdf(0.4,2,3) is 0.5248")
val res = beta_cdf(0.4, 2.0, 3.0)
expect(_approx(res, 0.5248, 0.0005)).to_be(true)
```

</details>

#### round-trip: beta_inv(beta_cdf(0.3,a=2,b=3)) ~= 0.3

- round-trip: beta_inv(beta_cdf(0.3,a=2,b=3)) ~= 0.3


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip: beta_inv(beta_cdf(0.3,a=2,b=3)) ~= 0.3")
val res = beta_inv(beta_cdf(0.3, 2.0, 3.0), 2.0, 3.0)
expect(_approx(res, 0.3, 0.00001)).to_be(true)
```

</details>

#### round-trip: beta_inv(beta_cdf(0.6,a=2,b=3)) ~= 0.6

- round-trip: beta_inv(beta_cdf(0.6,a=2,b=3)) ~= 0.6


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip: beta_inv(beta_cdf(0.6,a=2,b=3)) ~= 0.6")
val res = beta_inv(beta_cdf(0.6, 2.0, 3.0), 2.0, 3.0)
expect(_approx(res, 0.6, 0.00001)).to_be(true)
```

</details>

#### beta_cdf domain error (a<=0) is NaN

- beta_cdf domain error (a<=0) is NaN


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("beta_cdf domain error (a<=0) is NaN")
val res = beta_cdf(0.4, 0.0, 3.0)
expect(_is_nan(res)).to_be(true)
```

</details>

### std.math.distributions (gamma)

#### gamma_cdf/gamma_inv

#### gamma_cdf(2,3,1) is 0.323324

- gamma_cdf(2,3,1) is 0.323324


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gamma_cdf(2,3,1) is 0.323324")
val res = gamma_cdf(2.0, 3.0, 1.0)
expect(_approx(res, 0.323324, 0.0005)).to_be(true)
```

</details>

#### round-trip: gamma_inv(gamma_cdf(1.5,shape=3,scale=1)) ~= 1.5

- round-trip: gamma_inv(gamma_cdf(1.5,shape=3,scale=1)) ~= 1.5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip: gamma_inv(gamma_cdf(1.5,shape=3,scale=1)) ~= 1.5")
val res = gamma_inv(gamma_cdf(1.5, 3.0, 1.0), 3.0, 1.0)
expect(_approx(res, 1.5, 0.00001)).to_be(true)
```

</details>

#### round-trip: gamma_inv(gamma_cdf(4.0,shape=3,scale=1)) ~= 4.0

- round-trip: gamma_inv(gamma_cdf(4.0,shape=3,scale=1)) ~= 4.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip: gamma_inv(gamma_cdf(4.0,shape=3,scale=1)) ~= 4.0")
val res = gamma_inv(gamma_cdf(4.0, 3.0, 1.0), 3.0, 1.0)
expect(_approx(res, 4.0, 0.00001)).to_be(true)
```

</details>

#### gamma_cdf domain error (shape<=0) is NaN

- gamma_cdf domain error (shape<=0) is NaN


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gamma_cdf domain error (shape<=0) is NaN")
val res = gamma_cdf(2.0, 0.0, 1.0)
expect(_is_nan(res)).to_be(true)
```

</details>

### std.math.distributions (binomial)

#### binom_pmf/binom_cdf

#### binom_pmf(3,10,0.5) is 0.1171875

- binom_pmf(3,10,0.5) is 0.1171875


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binom_pmf(3,10,0.5) is 0.1171875")
val res = binom_pmf(3, 10, 0.5)
expect(_approx(res, 0.1171875, 0.0000001)).to_be(true)
```

</details>

#### binom_cdf(3,10,0.5) is 0.171875

- binom_cdf(3,10,0.5) is 0.171875


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binom_cdf(3,10,0.5) is 0.171875")
val res = binom_cdf(3, 10, 0.5)
expect(_approx(res, 0.171875, 0.0000001)).to_be(true)
```

</details>

#### binom_pmf(0,5,0.0) is 1.0 (0^0 = 1 convention)

- binom_pmf(0,5,0.0) is 1.0 (0^0 = 1 convention)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binom_pmf(0,5,0.0) is 1.0 (0^0 = 1 convention)")
val res = binom_pmf(0, 5, 0.0)
expect(_approx(res, 1.0, 0.0000001)).to_be(true)
```

</details>

#### binom_pmf domain error (k>n) is NaN

- binom_pmf domain error (k>n) is NaN


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binom_pmf domain error (k>n) is NaN")
val res = binom_pmf(11, 10, 0.5)
expect(_is_nan(res)).to_be(true)
```

</details>

### std.math.distributions (Poisson)

#### poisson_pmf/poisson_cdf

#### poisson_pmf(2,3) is 0.2240418

- poisson_pmf(2,3) is 0.2240418


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("poisson_pmf(2,3) is 0.2240418")
val res = poisson_pmf(2, 3.0)
expect(_approx(res, 0.2240418, 0.0000005)).to_be(true)
```

</details>

#### poisson_pmf(0,0) is 1.0 (0^0 = 1 convention)

- poisson_pmf(0,0) is 1.0 (0^0 = 1 convention)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("poisson_pmf(0,0) is 1.0 (0^0 = 1 convention)")
val res = poisson_pmf(0, 0.0)
expect(_approx(res, 1.0, 0.0000001)).to_be(true)
```

</details>

#### poisson_pmf domain error (lambda<0) is NaN

- poisson_pmf domain error (lambda<0) is NaN


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("poisson_pmf domain error (lambda<0) is NaN")
val res = poisson_pmf(2, -1.0)
expect(_is_nan(res)).to_be(true)
```

</details>

### std.math.distributions (exponential)

#### expon_cdf

#### expon_cdf(1,2) is 1 - e^-2 = 0.8646647

- expon_cdf(1,2) is 1 - e^-2 = 0.8646647


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expon_cdf(1,2) is 1 - e^-2 = 0.8646647")
val res = expon_cdf(1.0, 2.0)
expect(_approx(res, 0.8646647, 0.0000005)).to_be(true)
```

</details>

#### expon_cdf domain error (lambda<=0) is NaN

- expon_cdf domain error (lambda<=0) is NaN


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expon_cdf domain error (lambda<=0) is NaN")
val res = expon_cdf(1.0, 0.0)
expect(_is_nan(res)).to_be(true)
```

</details>

### std.math.distributions (hypergeometric)

#### hypgeom_pmf

#### hypgeom_pmf(1,4,8,20) is C(8,1)*C(12,3)/C(20,4) = 0.363260...

- hypgeom_pmf(1,4,8,20) is C(8,1)*C(12,3)/C(20,4) = 0.363260...


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hypgeom_pmf(1,4,8,20) is C(8,1)*C(12,3)/C(20,4) = 0.363260...")
val res = hypgeom_pmf(1, 4, 8, 20)
expect(_approx(res, 0.36326, 0.0001)).to_be(true)
```

</details>

#### hypgeom_pmf domain error (k>draws) is NaN

- hypgeom_pmf domain error (k>draws) is NaN


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hypgeom_pmf domain error (k>draws) is NaN")
val res = hypgeom_pmf(5, 4, 8, 20)
expect(_is_nan(res)).to_be(true)
```

</details>

### std.math.distributions (negative binomial)

#### negbinom_pmf

#### negbinom_pmf(2,3,0.5) is C(4,2)*0.5^3*0.5^2 = 6/32 = 0.1875

- negbinom_pmf(2,3,0.5) is C(4,2)*0.5^3*0.5^2 = 6/32 = 0.1875


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negbinom_pmf(2,3,0.5) is C(4,2)*0.5^3*0.5^2 = 6/32 = 0.1875")
val res = negbinom_pmf(2, 3, 0.5)
expect(_approx(res, 0.1875, 0.0000001)).to_be(true)
```

</details>

#### negbinom_pmf domain error (s<1) is NaN

- negbinom_pmf domain error (s<1) is NaN


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negbinom_pmf domain error (s<1) is NaN")
val res = negbinom_pmf(2, 0, 0.5)
expect(_is_nan(res)).to_be(true)
```

</details>

### std.math.distributions (Weibull)

#### weibull_cdf

#### weibull_cdf(2,1.5,3) is 1 - exp(-(2/3)^1.5) ~= 0.419770

- weibull_cdf(2,1.5,3) is 1 - exp(-(2/3)^1.5) ~= 0.419770


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("weibull_cdf(2,1.5,3) is 1 - exp(-(2/3)^1.5) ~= 0.419770")
val res = weibull_cdf(2.0, 1.5, 3.0)
expect(_approx(res, 0.419770, 0.000001)).to_be(true)
```

</details>

#### weibull_cdf(0,shape,scale) is 0.0

- weibull_cdf(0,shape,scale) is 0.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("weibull_cdf(0,shape,scale) is 0.0")
val res = weibull_cdf(0.0, 1.5, 3.0)
expect(_approx(res, 0.0, 0.0000001)).to_be(true)
```

</details>

#### weibull_cdf domain error (shape<=0) is NaN

- weibull_cdf domain error (shape<=0) is NaN


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("weibull_cdf domain error (shape<=0) is NaN")
val res = weibull_cdf(2.0, 0.0, 3.0)
expect(_is_nan(res)).to_be(true)
```

</details>

#### weibull_pdf

#### weibull_pdf(2,1.5,3) is ~0.2366

- weibull_pdf(2,1.5,3) is ~0.2366


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("weibull_pdf(2,1.5,3) is ~0.2366")
val res = weibull_pdf(2.0, 1.5, 3.0)
expect(_approx(res, 0.2366, 0.001)).to_be(true)
```

</details>

#### weibull_pdf(0,shape,scale) is 0.0

- weibull_pdf(0,shape,scale) is 0.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("weibull_pdf(0,shape,scale) is 0.0")
val res = weibull_pdf(0.0, 1.5, 3.0)
expect(_approx(res, 0.0, 0.0000001)).to_be(true)
```

</details>

#### weibull_pdf domain error (shape<=0) is NaN

- weibull_pdf domain error (shape<=0) is NaN


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("weibull_pdf domain error (shape<=0) is NaN")
val res = weibull_pdf(2.0, 0.0, 3.0)
expect(_is_nan(res)).to_be(true)
```

</details>

#### weibull_pdf domain error (scale<=0) is NaN

- weibull_pdf domain error (scale<=0) is NaN


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("weibull_pdf domain error (scale<=0) is NaN")
val res = weibull_pdf(2.0, 1.5, 0.0)
expect(_is_nan(res)).to_be(true)
```

</details>

#### weibull_pdf domain error (x<0) is NaN

- weibull_pdf domain error (x<0) is NaN


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("weibull_pdf domain error (x<0) is NaN")
val res = weibull_pdf(-1.0, 1.5, 3.0)
expect(_is_nan(res)).to_be(true)
```

</details>

### std.math.distributions (log-normal)

#### lognorm_cdf/lognorm_inv

#### lognorm_cdf(4,3.5,1.2) is 0.0390836

- lognorm_cdf(4,3.5,1.2) is 0.0390836


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lognorm_cdf(4,3.5,1.2) is 0.0390836")
val res = lognorm_cdf(4.0, 3.5, 1.2)
expect(_approx(res, 0.0390836, 0.000001)).to_be(true)
```

</details>

#### round-trip: lognorm_inv(lognorm_cdf(4.0,3.5,1.2)) ~= 4.0

- round-trip: lognorm_inv(lognorm_cdf(4.0,3.5,1.2)) ~= 4.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip: lognorm_inv(lognorm_cdf(4.0,3.5,1.2)) ~= 4.0")
val res = lognorm_inv(lognorm_cdf(4.0, 3.5, 1.2), 3.5, 1.2)
expect(_approx(res, 4.0, 0.0001)).to_be(true)
```

</details>

#### lognorm_cdf domain error (x<=0) is NaN

- lognorm_cdf domain error (x<=0) is NaN


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lognorm_cdf domain error (x<=0) is NaN")
val res = lognorm_cdf(0.0, 3.5, 1.2)
expect(_is_nan(res)).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/math/distributions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering std.math.distributions (normal), std.math.distributions (Student's t), std.math.distributions (chi-squared), std.math.distributions (F distribution), std.math.distributions (beta), std.math.distributions (gamma), std.math.distributions (binomial), std.math.distributions (Poisson), std.math.distributions (exponential), std.math.distributions (hypergeometric), std.math.distributions (negative binomial), std.math.distributions (Weibull), std.math.distributions (log-normal).
- std.math.distributions (normal)
- std.math.distributions (Student's t)
- std.math.distributions (chi-squared)
- std.math.distributions (F distribution)
- std.math.distributions (beta)
- std.math.distributions (gamma)
- std.math.distributions (binomial)
- std.math.distributions (Poisson)
- std.math.distributions (exponential)
- std.math.distributions (hypergeometric)
- std.math.distributions (negative binomial)
- std.math.distributions (Weibull)
- std.math.distributions (log-normal)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 55 |
| Active scenarios | 55 |
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

- Canonical SPipe generation for source `b388b2e9570dfc3e4ef89cba19100730ae6b700e625cdd8fadd3e5e73e40c987`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b388b2e9570dfc3e4ef89cba19100730ae6b700e625cdd8fadd3e5e73e40c987`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b388b2e9570dfc3e4ef89cba19100730ae6b700e625cdd8fadd3e5e73e40c987`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/math/distributions_spec.spl
mirror: doc/06_spec/01_unit/lib/common/math/distributions_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/math/distributions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/math/distributions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/math/distributions_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'norm_pdf(0,0,1) is 1/sqrt(2*pi) ~ 0.398942' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math/distributions_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'norm_pdf domain error (sd<=0) is NaN' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math/distributions_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'norm_cdf(1.96,0,1) is 0.9750021' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
