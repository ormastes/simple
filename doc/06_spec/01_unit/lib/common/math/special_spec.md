# Special Specification

> Tests covering std.math.special (gamma / beta), std.math.special (error function), std.math.special (incomplete beta), std.math.special (incomplete gamma), std.math.special (powf), std.math.special (factorial / combinatorics), std.math.special (trigonometric).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 55 | 55 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Special Specification

## Scenarios

### std.math.special (gamma / beta)

#### gamma_fn

#### gamma_fn(5) is 24 (4! since Gamma(n) = (n-1)!)

- gamma_fn(5) is 24 (4! since Gamma(n) = (n-1)!)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gamma_fn(5) is 24 (4! since Gamma(n) = (n-1)!)")
val res = gamma_fn(5.0)
expect(_approx(res, 24.0, 0.0001)).to_be(true)
```

</details>

#### gamma_fn(1) is 1

- gamma_fn(1) is 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gamma_fn(1) is 1")
val res = gamma_fn(1.0)
expect(_approx(res, 1.0, 0.0001)).to_be(true)
```

</details>

#### gamma_fn(0.5) is sqrt(pi) ~ 1.772454

- gamma_fn(0.5) is sqrt(pi) ~ 1.772454


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gamma_fn(0.5) is sqrt(pi) ~ 1.772454")
val res = gamma_fn(0.5)
expect(_approx(res, 1.7724538509, 0.0001)).to_be(true)
```

</details>

#### gamma_ln

#### gamma_ln(10) is ln(362880) ~ 12.801827

- gamma_ln(10) is ln(362880) ~ 12.801827


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gamma_ln(10) is ln(362880) ~ 12.801827")
val res = gamma_ln(10.0)
expect(_approx(res, 12.801827480081467, 0.0001)).to_be(true)
```

</details>

#### gamma_ln(1) is 0

- gamma_ln(1) is 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gamma_ln(1) is 0")
val res = gamma_ln(1.0)
expect(_approx(res, 0.0, 0.0001)).to_be(true)
```

</details>

#### beta_fn

#### beta_fn(2,3) is 1/12 ~ 0.083333

- beta_fn(2,3) is 1/12 ~ 0.083333


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("beta_fn(2,3) is 1/12 ~ 0.083333")
val res = beta_fn(2.0, 3.0)
expect(_approx(res, 0.08333333333, 0.0001)).to_be(true)
```

</details>

### std.math.special (error function)

#### erf

#### erf(1) is 0.8427008

- erf(1) is 0.8427008


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("erf(1) is 0.8427008")
val res = erf(1.0)
expect(_approx(res, 0.8427008, 0.0001)).to_be(true)
```

</details>

#### erf(0) is 0

- erf(0) is 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("erf(0) is 0")
val res = erf(0.0)
expect(_approx(res, 0.0, 0.0001)).to_be(true)
```

</details>

#### erf is odd: erf(-1) is -erf(1)

- erf is odd: erf(-1) is -erf(1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("erf is odd: erf(-1) is -erf(1)")
val neg = erf(-1.0)
val pos = erf(1.0)
expect(_approx(neg, 0.0 - pos, 0.0000001)).to_be(true)
```

</details>

#### erfc

#### erfc(0.5) is 0.4795001

- erfc(0.5) is 0.4795001


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("erfc(0.5) is 0.4795001")
val res = erfc(0.5)
expect(_approx(res, 0.4795001, 0.0001)).to_be(true)
```

</details>

#### erfc(0) is 1

- erfc(0) is 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("erfc(0) is 1")
val res = erfc(0.0)
expect(_approx(res, 1.0, 0.0001)).to_be(true)
```

</details>

### std.math.special (incomplete beta)

#### incomplete_beta

#### incomplete_beta(2,3,0.4) is 0.5248

- incomplete_beta(2,3,0.4) is 0.5248


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("incomplete_beta(2,3,0.4) is 0.5248")
val res = incomplete_beta(2.0, 3.0, 0.4)
expect(_approx(res, 0.5248, 0.0001)).to_be(true)
```

</details>

#### incomplete_beta(a,b,0.0) is 0.0 (clamped, not an error)

- incomplete_beta(a,b,0.0) is 0.0 (clamped, not an error)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("incomplete_beta(a,b,0.0) is 0.0 (clamped, not an error)")
val res = incomplete_beta(2.0, 3.0, 0.0)
expect(_approx(res, 0.0, 0.0000001)).to_be(true)
```

</details>

#### incomplete_beta(a,b,1.0) is 1.0 (clamped, not an error)

- incomplete_beta(a,b,1.0) is 1.0 (clamped, not an error)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("incomplete_beta(a,b,1.0) is 1.0 (clamped, not an error)")
val res = incomplete_beta(2.0, 3.0, 1.0)
expect(_approx(res, 1.0, 0.0000001)).to_be(true)
```

</details>

#### incomplete_beta_inv round-trip

#### incomplete_beta_inv(2,3, incomplete_beta(2,3,0.4)) is ~0.4

- incomplete_beta_inv(2,3, incomplete_beta(2,3,0.4)) is ~0.4


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("incomplete_beta_inv(2,3, incomplete_beta(2,3,0.4)) is ~0.4")
val p = incomplete_beta(2.0, 3.0, 0.4)
val res = incomplete_beta_inv(2.0, 3.0, p)
expect(_approx(res, 0.4, 0.000001)).to_be(true)
```

</details>

#### incomplete_beta_inv(2,3, incomplete_beta(2,3,0.2)) is ~0.2

- incomplete_beta_inv(2,3, incomplete_beta(2,3,0.2)) is ~0.2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("incomplete_beta_inv(2,3, incomplete_beta(2,3,0.2)) is ~0.2")
val p = incomplete_beta(2.0, 3.0, 0.2)
val res = incomplete_beta_inv(2.0, 3.0, p)
expect(_approx(res, 0.2, 0.000001)).to_be(true)
```

</details>

#### incomplete_beta_inv(5,2, incomplete_beta(5,2,0.7)) is ~0.7

- incomplete_beta_inv(5,2, incomplete_beta(5,2,0.7)) is ~0.7


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("incomplete_beta_inv(5,2, incomplete_beta(5,2,0.7)) is ~0.7")
val p = incomplete_beta(5.0, 2.0, 0.7)
val res = incomplete_beta_inv(5.0, 2.0, p)
expect(_approx(res, 0.7, 0.000001)).to_be(true)
```

</details>

### std.math.special (incomplete gamma)

#### incomplete_gamma_p

#### incomplete_gamma_p(3,2) is 0.323324

- incomplete_gamma_p(3,2) is 0.323324


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("incomplete_gamma_p(3,2) is 0.323324")
val res = incomplete_gamma_p(3.0, 2.0)
expect(_approx(res, 0.323324, 0.000001)).to_be(true)
```

</details>

#### incomplete_gamma_p(a,0.0) is 0.0 (clamped, not an error)

- incomplete_gamma_p(a,0.0) is 0.0 (clamped, not an error)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("incomplete_gamma_p(a,0.0) is 0.0 (clamped, not an error)")
val res = incomplete_gamma_p(3.0, 0.0)
expect(_approx(res, 0.0, 0.0000001)).to_be(true)
```

</details>

#### incomplete_gamma_p_inv round-trip

#### incomplete_gamma_p_inv(3, incomplete_gamma_p(3,2)) is ~2

- incomplete_gamma_p_inv(3, incomplete_gamma_p(3,2)) is ~2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("incomplete_gamma_p_inv(3, incomplete_gamma_p(3,2)) is ~2")
val p = incomplete_gamma_p(3.0, 2.0)
val res = incomplete_gamma_p_inv(3.0, p)
expect(_approx(res, 2.0, 0.000001)).to_be(true)
```

</details>

#### incomplete_gamma_p_inv(5, incomplete_gamma_p(5,4)) is ~4

- incomplete_gamma_p_inv(5, incomplete_gamma_p(5,4)) is ~4


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("incomplete_gamma_p_inv(5, incomplete_gamma_p(5,4)) is ~4")
val p = incomplete_gamma_p(5.0, 4.0)
val res = incomplete_gamma_p_inv(5.0, p)
expect(_approx(res, 4.0, 0.000001)).to_be(true)
```

</details>

#### incomplete_gamma_p_inv(2, incomplete_gamma_p(2,1)) is ~1

- incomplete_gamma_p_inv(2, incomplete_gamma_p(2,1)) is ~1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("incomplete_gamma_p_inv(2, incomplete_gamma_p(2,1)) is ~1")
val p = incomplete_gamma_p(2.0, 1.0)
val res = incomplete_gamma_p_inv(2.0, p)
expect(_approx(res, 1.0, 0.000001)).to_be(true)
```

</details>

### std.math.special (powf)

#### powf(2, 0.5) is 1.4142136

- powf(2, 0.5) is 1.4142136


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("powf(2, 0.5) is 1.4142136")
val res = powf(2.0, 0.5)
expect(_approx(res, 1.4142136, 0.0001)).to_be(true)
```

</details>

#### powf(4, 0.5) is 2.0

- powf(4, 0.5) is 2.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("powf(4, 0.5) is 2.0")
val res = powf(4.0, 0.5)
expect(_approx(res, 2.0, 0.0001)).to_be(true)
```

</details>

#### powf(2, 10) is 1024.0

- powf(2, 10) is 1024.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("powf(2, 10) is 1024.0")
val res = powf(2.0, 10.0)
expect(_approx(res, 1024.0, 0.01)).to_be(true)
```

</details>

#### powf on non-positive base returns 0.0 (documented quirk, not an error)

- powf on non-positive base returns 0.0 (documented quirk, not an error)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("powf on non-positive base returns 0.0 (documented quirk, not an error)")
val res = powf(-2.0, 2.0)
expect(_approx(res, 0.0, 0.0000001)).to_be(true)
```

</details>

### std.math.special (factorial / combinatorics)

#### factorial

#### factorial(5) is 120

- factorial(5) is 120


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("factorial(5) is 120")
val res = factorial(5)
expect(_approx(res, 120.0, 0.0001)).to_be(true)
```

</details>

#### factorial(0) is 1

- factorial(0) is 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("factorial(0) is 1")
val res = factorial(0)
expect(_approx(res, 1.0, 0.0001)).to_be(true)
```

</details>

#### factorial2

#### factorial2(7) is 105 (7*5*3*1)

- factorial2(7) is 105 (7*5*3*1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("factorial2(7) is 105 (7*5*3*1)")
val res = factorial2(7)
expect(_approx(res, 105.0, 0.0001)).to_be(true)
```

</details>

#### factorial2(8) is 384 (8*6*4*2)

- factorial2(8) is 384 (8*6*4*2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("factorial2(8) is 384 (8*6*4*2)")
val res = factorial2(8)
expect(_approx(res, 384.0, 0.0001)).to_be(true)
```

</details>

#### combin

#### combin(10,3) is 120

- combin(10,3) is 120


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combin(10,3) is 120")
val res = combin(10, 3)
expect(_approx(res, 120.0, 0.0001)).to_be(true)
```

</details>

#### combin(5,0) is 1

- combin(5,0) is 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combin(5,0) is 1")
val res = combin(5, 0)
expect(_approx(res, 1.0, 0.0001)).to_be(true)
```

</details>

#### combina

#### combina(4,3) is 20

- combina(4,3) is 20


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combina(4,3) is 20")
val res = combina(4, 3)
expect(_approx(res, 20.0, 0.0001)).to_be(true)
```

</details>

#### combina(0,0) is 1 (k==0 special case)

- combina(0,0) is 1 (k==0 special case)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combina(0,0) is 1 (k==0 special case)")
val res = combina(0, 0)
expect(_approx(res, 1.0, 0.0001)).to_be(true)
```

</details>

### std.math.special (trigonometric)

#### fabs

#### fabs(-3.5) is 3.5

- fabs(-3.5) is 3.5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fabs(-3.5) is 3.5")
val res = fabs(-3.5)
expect(_approx(res, 3.5, 0.0001)).to_be(true)
```

</details>

#### fabs(3.5) is 3.5

- fabs(3.5) is 3.5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fabs(3.5) is 3.5")
val res = fabs(3.5)
expect(_approx(res, 3.5, 0.0001)).to_be(true)
```

</details>

#### fabs(0) is 0

- fabs(0) is 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fabs(0) is 0")
val res = fabs(0.0)
expect(_approx(res, 0.0, 0.0001)).to_be(true)
```

</details>

#### sin_f64

#### sin_f64(1.5707963) is ~1.0 (sin(π/2) ≈ 1)

- sin_f64(1.5707963) is ~1.0 (sin(π/2) ≈ 1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sin_f64(1.5707963) is ~1.0 (sin(π/2) ≈ 1)")
val res = sin_f64(1.5707963)
expect(_approx(res, 1.0, 0.0001)).to_be(true)
```

</details>

#### sin_f64(0) is 0

- sin_f64(0) is 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sin_f64(0) is 0")
val res = sin_f64(0.0)
expect(_approx(res, 0.0, 0.0001)).to_be(true)
```

</details>

#### sin_f64(π/6) is 0.5

- sin_f64(π/6) is 0.5


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sin_f64(π/6) is 0.5")
val pi_over_6 = 3.141592653589793 / 6.0
val res = sin_f64(pi_over_6)
expect(_approx(res, 0.5, 0.0001)).to_be(true)
```

</details>

#### cos_f64

#### cos_f64(0) is 1

- cos_f64(0) is 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cos_f64(0) is 1")
val res = cos_f64(0.0)
expect(_approx(res, 1.0, 0.0001)).to_be(true)
```

</details>

#### cos_f64(π) is -1

- cos_f64(π) is -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cos_f64(π) is -1")
val pi = 3.141592653589793
val res = cos_f64(pi)
expect(_approx(res, -1.0, 0.0001)).to_be(true)
```

</details>

#### cos_f64(π/3) is 0.5

- cos_f64(π/3) is 0.5


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cos_f64(π/3) is 0.5")
val pi_over_3 = 3.141592653589793 / 3.0
val res = cos_f64(pi_over_3)
expect(_approx(res, 0.5, 0.0001)).to_be(true)
```

</details>

#### tan_f64

#### tan_f64(π/4) is ~1.0

- tan_f64(π/4) is ~1.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tan_f64(π/4) is ~1.0")
val pi_over_4 = 3.141592653589793 / 4.0
val res = tan_f64(pi_over_4)
expect(_approx(res, 1.0, 0.0001)).to_be(true)
```

</details>

#### tan_f64(0) is 0

- tan_f64(0) is 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tan_f64(0) is 0")
val res = tan_f64(0.0)
expect(_approx(res, 0.0, 0.0001)).to_be(true)
```

</details>

#### atan_f64

#### atan_f64(1) is π/4 ~0.7853982

- atan_f64(1) is π/4 ~0.7853982


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("atan_f64(1) is π/4 ~0.7853982")
val res = atan_f64(1.0)
expect(_approx(res, 0.7853982, 0.0001)).to_be(true)
```

</details>

#### atan_f64(0) is 0

- atan_f64(0) is 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("atan_f64(0) is 0")
val res = atan_f64(0.0)
expect(_approx(res, 0.0, 0.0001)).to_be(true)
```

</details>

#### atan_f64(-1) is -π/4 ~-0.7853982

- atan_f64(-1) is -π/4 ~-0.7853982


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("atan_f64(-1) is -π/4 ~-0.7853982")
val res = atan_f64(-1.0)
expect(_approx(res, -0.7853982, 0.0001)).to_be(true)
```

</details>

#### atan2_f64

#### atan2_f64(1,1) is π/4 ~0.7853982

- atan2_f64(1,1) is π/4 ~0.7853982


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("atan2_f64(1,1) is π/4 ~0.7853982")
val res = atan2_f64(1.0, 1.0)
expect(_approx(res, 0.7853982, 0.0001)).to_be(true)
```

</details>

#### atan2_f64(0,1) is 0

- atan2_f64(0,1) is 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("atan2_f64(0,1) is 0")
val res = atan2_f64(0.0, 1.0)
expect(_approx(res, 0.0, 0.0001)).to_be(true)
```

</details>

#### atan2_f64(1,0) is π/2 ~1.5707963

- atan2_f64(1,0) is π/2 ~1.5707963


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("atan2_f64(1,0) is π/2 ~1.5707963")
val res = atan2_f64(1.0, 0.0)
expect(_approx(res, 1.5707963, 0.0001)).to_be(true)
```

</details>

#### atan2_f64(1,-1) is 3π/4 ~2.356194

- atan2_f64(1,-1) is 3π/4 ~2.356194


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("atan2_f64(1,-1) is 3π/4 ~2.356194")
val res = atan2_f64(1.0, -1.0)
expect(_approx(res, 2.356194, 0.0001)).to_be(true)
```

</details>

#### fact_i64

#### fact_i64(10) is 3628800 (10!)

- fact_i64(10) is 3628800 (10!)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fact_i64(10) is 3628800 (10!)")
val res = fact_i64(10)
expect(_approx(res, 3628800.0, 0.0001)).to_be(true)
```

</details>

#### fact_i64(0) is 1

- fact_i64(0) is 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fact_i64(0) is 1")
val res = fact_i64(0)
expect(_approx(res, 1.0, 0.0001)).to_be(true)
```

</details>

#### fact_i64(5) is 120

- fact_i64(5) is 120


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fact_i64(5) is 120")
val res = fact_i64(5)
expect(_approx(res, 120.0, 0.0001)).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/math/special_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering std.math.special (gamma / beta), std.math.special (error function), std.math.special (incomplete beta), std.math.special (incomplete gamma), std.math.special (powf), std.math.special (factorial / combinatorics), std.math.special (trigonometric).
- std.math.special (gamma / beta)
- std.math.special (error function)
- std.math.special (incomplete beta)
- std.math.special (incomplete gamma)
- std.math.special (powf)
- std.math.special (factorial / combinatorics)
- std.math.special (trigonometric)

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

- Canonical SPipe generation for source `467edce10b46d71e44cbab59d713c61cfee7e67c492d6707eb6a1ff930204e93`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `467edce10b46d71e44cbab59d713c61cfee7e67c492d6707eb6a1ff930204e93`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `467edce10b46d71e44cbab59d713c61cfee7e67c492d6707eb6a1ff930204e93`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/math/special_spec.spl
mirror: doc/06_spec/01_unit/lib/common/math/special_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/math/special_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/math/special_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/math/special_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gamma_fn(5) is 24 (4! since Gamma(n) = (n-1)!)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math/special_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gamma_fn(1) is 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math/special_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gamma_fn(0.5) is sqrt(pi) ~ 1.772454' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
