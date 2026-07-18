# Math Comprehensive Specification

> <details>

<!-- sdn-diagram:id=math_comprehensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_comprehensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_comprehensive_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_comprehensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 138 | 138 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Comprehensive Specification

## Scenarios

### Math constants

#### MATH_PI is approximately 3.14159

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val close = math_is_close(MATH_PI, 3.14159, 0.001)
expect(close).to_equal(true)
```

</details>

#### MATH_E is approximately 2.71828

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val close = math_is_close(MATH_E, 2.71828, 0.001)
expect(close).to_equal(true)
```

</details>

#### MATH_TAU is approximately 2 * PI

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val double_pi = MATH_PI * 2.0
val close = math_is_close(MATH_TAU, double_pi, 0.0001)
expect(close).to_equal(true)
```

</details>

#### MATH_INF is a very large number

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val big = 1000000.0
val result = MATH_INF > big
expect(result).to_equal(true)
```

</details>

### math_abs (f64)

#### returns positive for negative input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_abs(-3.5)
val close = math_is_close(result, 3.5, 0.001)
expect(close).to_equal(true)
```

</details>

#### returns same for positive input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_abs(7.2)
val close = math_is_close(result, 7.2, 0.001)
expect(close).to_equal(true)
```

</details>

#### returns 0.0 for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_abs(0.0)
val close = math_is_close(result, 0.0, 0.001)
expect(close).to_equal(true)
```

</details>

### math_abs_i64

#### returns positive for negative input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_abs_i64(-42)).to_equal(42)
```

</details>

#### returns same for positive input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_abs_i64(17)).to_equal(17)
```

</details>

#### returns 0 for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_abs_i64(0)).to_equal(0)
```

</details>

#### handles large negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_abs_i64(-999999)).to_equal(999999)
```

</details>

### math_min (f64)

#### returns smaller of two positive values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_min(3.0, 5.0)
val close = math_is_close(result, 3.0, 0.001)
expect(close).to_equal(true)
```

</details>

#### returns negative when one is negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_min(-2.0, 4.0)
val close = math_is_close(result, -2.0, 0.001)
expect(close).to_equal(true)
```

</details>

#### returns the value when both are equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_min(7.0, 7.0)
val close = math_is_close(result, 7.0, 0.001)
expect(close).to_equal(true)
```

</details>

### math_max (f64)

#### returns larger of two positive values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_max(3.0, 5.0)
val close = math_is_close(result, 5.0, 0.001)
expect(close).to_equal(true)
```

</details>

#### returns positive when one is negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_max(-2.0, 4.0)
val close = math_is_close(result, 4.0, 0.001)
expect(close).to_equal(true)
```

</details>

#### returns the value when both are equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_max(7.0, 7.0)
val close = math_is_close(result, 7.0, 0.001)
expect(close).to_equal(true)
```

</details>

### math_min_i64

#### returns smaller value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_min_i64(3, 8)).to_equal(3)
```

</details>

#### handles negatives

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_min_i64(-10, 5)).to_equal(-10)
```

</details>

#### handles equal values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_min_i64(4, 4)).to_equal(4)
```

</details>

### math_max_i64

#### returns larger value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_max_i64(3, 8)).to_equal(8)
```

</details>

#### handles negatives

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_max_i64(-10, 5)).to_equal(5)
```

</details>

#### handles equal values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_max_i64(4, 4)).to_equal(4)
```

</details>

### math_clamp (f64)

#### returns value when within range

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_clamp(5.0, 0.0, 10.0)
val close = math_is_close(result, 5.0, 0.001)
expect(close).to_equal(true)
```

</details>

#### returns min when below range

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_clamp(-3.0, 0.0, 10.0)
val close = math_is_close(result, 0.0, 0.001)
expect(close).to_equal(true)
```

</details>

#### returns max when above range

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_clamp(15.0, 0.0, 10.0)
val close = math_is_close(result, 10.0, 0.001)
expect(close).to_equal(true)
```

</details>

### math_clamp_i64

#### returns value when within range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_clamp_i64(5, 0, 10)).to_equal(5)
```

</details>

#### returns min when below range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_clamp_i64(-3, 0, 10)).to_equal(0)
```

</details>

#### returns max when above range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_clamp_i64(15, 0, 10)).to_equal(10)
```

</details>

#### handles boundary values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_clamp_i64(0, 0, 10)).to_equal(0)
expect(math_clamp_i64(10, 0, 10)).to_equal(10)
```

</details>

### math_sign (f64)

#### returns -1.0 for negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_sign(-7.5)
val close = math_is_close(result, -1.0, 0.001)
expect(close).to_equal(true)
```

</details>

#### returns 1.0 for positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_sign(3.2)
val close = math_is_close(result, 1.0, 0.001)
expect(close).to_equal(true)
```

</details>

#### returns 0.0 for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_sign(0.0)
val close = math_is_close(result, 0.0, 0.001)
expect(close).to_equal(true)
```

</details>

### math_sign_i64

#### returns -1 for negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sign_i64(-42)).to_equal(-1)
```

</details>

#### returns 1 for positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sign_i64(99)).to_equal(1)
```

</details>

#### returns 0 for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_sign_i64(0)).to_equal(0)
```

</details>

### math_lerp

#### returns a when t=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_lerp(10.0, 20.0, 0.0)
val close = math_is_close(result, 10.0, 0.001)
expect(close).to_equal(true)
```

</details>

#### returns b when t=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_lerp(10.0, 20.0, 1.0)
val close = math_is_close(result, 20.0, 0.001)
expect(close).to_equal(true)
```

</details>

#### returns midpoint when t=0.5

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_lerp(10.0, 20.0, 0.5)
val close = math_is_close(result, 15.0, 0.001)
expect(close).to_equal(true)
```

</details>

#### handles t=0.25

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_lerp(0.0, 100.0, 0.25)
val close = math_is_close(result, 25.0, 0.001)
expect(close).to_equal(true)
```

</details>

### math_is_close

#### returns true for identical values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_is_close(5.0, 5.0, 0.01)
expect(result).to_equal(true)
```

</details>

#### returns true for values within tolerance

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_is_close(5.0, 5.005, 0.01)
expect(result).to_equal(true)
```

</details>

#### returns false for values outside tolerance

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_is_close(5.0, 6.0, 0.01)
expect(result).to_equal(false)
```

</details>

#### handles negative differences

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_is_close(3.0, 2.999, 0.01)
expect(result).to_equal(true)
```

</details>

### math_gcd

#### computes gcd of 12 and 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_gcd(12, 8)).to_equal(4)
```

</details>

#### computes gcd of coprime numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_gcd(7, 13)).to_equal(1)
```

</details>

#### handles zero argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_gcd(5, 0)).to_equal(5)
expect(math_gcd(0, 5)).to_equal(5)
```

</details>

#### handles negative arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_gcd(-12, 8)).to_equal(4)
expect(math_gcd(12, -8)).to_equal(4)
```

</details>

#### computes gcd of equal values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_gcd(6, 6)).to_equal(6)
```

</details>

### math_lcm

#### computes lcm of 4 and 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_lcm(4, 6)).to_equal(12)
```

</details>

#### computes lcm of coprime numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_lcm(3, 5)).to_equal(15)
```

</details>

#### returns 0 when either argument is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_lcm(0, 5)).to_equal(0)
expect(math_lcm(5, 0)).to_equal(0)
```

</details>

#### computes lcm of 7 and 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_lcm(7, 3)).to_equal(21)
```

</details>

### math_pow_i64

#### computes 2^10

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_pow_i64(2, 10)).to_equal(1024)
```

</details>

#### computes 3^5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_pow_i64(3, 5)).to_equal(243)
```

</details>

#### returns 1 for exponent 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_pow_i64(99, 0)).to_equal(1)
```

</details>

#### returns 0 for negative exponent

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_pow_i64(2, -1)).to_equal(0)
```

</details>

#### computes 1^large

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_pow_i64(1, 1000)).to_equal(1)
```

</details>

#### computes 5^3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_pow_i64(5, 3)).to_equal(125)
```

</details>

### math_factorial

#### computes 0! = 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_factorial(0)).to_equal(1)
```

</details>

#### computes 1! = 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_factorial(1)).to_equal(1)
```

</details>

#### computes 5! = 120

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_factorial(5)).to_equal(120)
```

</details>

#### computes 10! = 3628800

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_factorial(10)).to_equal(3628800)
```

</details>

#### returns 1 for negative input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_factorial(-5)).to_equal(1)
```

</details>

### math_to_radians

#### converts 0 degrees to 0 radians

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_to_radians(0.0)
val close = math_is_close(result, 0.0, 0.001)
expect(close).to_equal(true)
```

</details>

#### converts 180 degrees to PI radians

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_to_radians(180.0)
val close = math_is_close(result, MATH_PI, 0.001)
expect(close).to_equal(true)
```

</details>

#### converts 360 degrees to TAU radians

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_to_radians(360.0)
val close = math_is_close(result, MATH_TAU, 0.001)
expect(close).to_equal(true)
```

</details>

#### converts 90 degrees to PI/2 radians

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_to_radians(90.0)
val expected = MATH_PI / 2.0
val close = math_is_close(result, expected, 0.001)
expect(close).to_equal(true)
```

</details>

### math_to_degrees

#### converts 0 radians to 0 degrees

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_to_degrees(0.0)
val close = math_is_close(result, 0.0, 0.001)
expect(close).to_equal(true)
```

</details>

#### converts PI radians to 180 degrees

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_to_degrees(MATH_PI)
val close = math_is_close(result, 180.0, 0.001)
expect(close).to_equal(true)
```

</details>

#### converts TAU radians to 360 degrees

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_to_degrees(MATH_TAU)
val close = math_is_close(result, 360.0, 0.001)
expect(close).to_equal(true)
```

</details>

#### round-trips degrees through radians

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = 45.0
val rad = math_to_radians(original)
val deg = math_to_degrees(rad)
val close = math_is_close(deg, original, 0.001)
expect(close).to_equal(true)
```

</details>

### abs_i64 (alias)

#### returns positive for negative input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(abs_i64(-15)).to_equal(15)
```

</details>

#### returns same for positive input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(abs_i64(15)).to_equal(15)
```

</details>

#### returns 0 for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(abs_i64(0)).to_equal(0)
```

</details>

### min_i64 (alias)

#### returns smaller value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(min_i64(2, 9)).to_equal(2)
```

</details>

#### handles negatives

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(min_i64(-5, -1)).to_equal(-5)
```

</details>

### max_i64 (alias)

#### returns larger value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(max_i64(2, 9)).to_equal(9)
```

</details>

#### handles negatives

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(max_i64(-5, -1)).to_equal(-1)
```

</details>

### clamp_i64 (alias)

#### clamps within range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp_i64(5, 0, 10)).to_equal(5)
```

</details>

#### clamps below minimum

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp_i64(-5, 0, 10)).to_equal(0)
```

</details>

#### clamps above maximum

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp_i64(20, 0, 10)).to_equal(10)
```

</details>

### sign_i64 (alias)

#### returns -1 for negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sign_i64(-3)).to_equal(-1)
```

</details>

#### returns 1 for positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sign_i64(3)).to_equal(1)
```

</details>

#### returns 0 for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sign_i64(0)).to_equal(0)
```

</details>

### pow_i64 (alias)

#### computes 2^8 = 256

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pow_i64(2, 8)).to_equal(256)
```

</details>

#### computes 10^3 = 1000

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pow_i64(10, 3)).to_equal(1000)
```

</details>

#### handles exponent 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pow_i64(42, 0)).to_equal(1)
```

</details>

### gcd (alias)

#### computes gcd of 18 and 12

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gcd(18, 12)).to_equal(6)
```

</details>

#### computes gcd of 100 and 75

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gcd(100, 75)).to_equal(25)
```

</details>

### lcm (alias)

#### computes lcm of 6 and 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lcm(6, 8)).to_equal(24)
```

</details>

#### computes lcm of 12 and 15

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lcm(12, 15)).to_equal(60)
```

</details>

### factorial (alias)

#### computes 7! = 5040

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(factorial(7)).to_equal(5040)
```

</details>

#### computes 3! = 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(factorial(3)).to_equal(6)
```

</details>

### binomial

#### computes C(5, 2) = 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(binomial(5, 2)).to_equal(10)
```

</details>

#### computes C(10, 3) = 120

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(binomial(10, 3)).to_equal(120)
```

</details>

#### returns 1 when k=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(binomial(10, 0)).to_equal(1)
```

</details>

#### returns 1 when k=n

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(binomial(5, 5)).to_equal(1)
```

</details>

#### returns 0 when k > n

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(binomial(3, 5)).to_equal(0)
```

</details>

#### computes C(6, 1) = 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(binomial(6, 1)).to_equal(6)
```

</details>

#### computes C(4, 2) = 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(binomial(4, 2)).to_equal(6)
```

</details>

### is_even

#### returns true for even numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_even(0)).to_equal(true)
expect(is_even(2)).to_equal(true)
expect(is_even(100)).to_equal(true)
```

</details>

#### returns false for odd numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_even(1)).to_equal(false)
expect(is_even(3)).to_equal(false)
expect(is_even(99)).to_equal(false)
```

</details>

#### handles negative even numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_even(-4)).to_equal(true)
```

</details>

#### handles negative odd numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_even(-3)).to_equal(false)
```

</details>

### is_odd

#### returns true for odd numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_odd(1)).to_equal(true)
expect(is_odd(3)).to_equal(true)
expect(is_odd(99)).to_equal(true)
```

</details>

#### returns false for even numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_odd(0)).to_equal(false)
expect(is_odd(2)).to_equal(false)
expect(is_odd(100)).to_equal(false)
```

</details>

#### handles negative odd numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_odd(-3)).to_equal(true)
```

</details>

#### handles negative even numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_odd(-4)).to_equal(false)
```

</details>

### is_divisible_by

#### returns true for divisible values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_divisible_by(10, 5)).to_equal(true)
expect(is_divisible_by(12, 3)).to_equal(true)
expect(is_divisible_by(100, 10)).to_equal(true)
```

</details>

#### returns false for non-divisible values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_divisible_by(10, 3)).to_equal(false)
expect(is_divisible_by(7, 2)).to_equal(false)
```

</details>

#### returns false when divisor is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_divisible_by(10, 0)).to_equal(false)
```

</details>

#### every number is divisible by 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_divisible_by(42, 1)).to_equal(true)
expect(is_divisible_by(0, 1)).to_equal(true)
```

</details>

### in_range_i64

#### returns true when value is within range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(in_range_i64(5, 0, 10)).to_equal(true)
```

</details>

#### returns true at boundaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(in_range_i64(0, 0, 10)).to_equal(true)
expect(in_range_i64(10, 0, 10)).to_equal(true)
```

</details>

#### returns false below range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(in_range_i64(-1, 0, 10)).to_equal(false)
```

</details>

#### returns false above range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(in_range_i64(11, 0, 10)).to_equal(false)
```

</details>

#### works with negative ranges

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(in_range_i64(-5, -10, -1)).to_equal(true)
expect(in_range_i64(0, -10, -1)).to_equal(false)
```

</details>

### sum_i64

#### sums a list of positive numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sum_i64([1, 2, 3, 4, 5])).to_equal(15)
```

</details>

#### sums an empty list to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sum_i64([])).to_equal(0)
```

</details>

#### sums a single-element list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sum_i64([42])).to_equal(42)
```

</details>

#### handles negative numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sum_i64([-1, -2, -3])).to_equal(-6)
```

</details>

#### handles mixed positive and negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sum_i64([10, -3, 5, -2])).to_equal(10)
```

</details>

### product_i64

#### multiplies a list of numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(product_i64([1, 2, 3, 4])).to_equal(24)
```

</details>

#### returns 1 for empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(product_i64([])).to_equal(1)
```

</details>

#### handles single-element list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(product_i64([7])).to_equal(7)
```

</details>

#### handles a zero in the list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(product_i64([5, 0, 3])).to_equal(0)
```

</details>

#### handles negative numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(product_i64([-2, 3])).to_equal(-6)
```

</details>

### average_i64

#### computes average of a list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = average_i64([2, 4, 6])
expect(result).to_equal(4)
```

</details>

#### returns nil for empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = average_i64([])
expect(result).to_be_nil()
```

</details>

#### computes average of single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = average_i64([10])
expect(result).to_equal(10)
```

</details>

#### truncates toward zero for integer division

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# [1, 2] -> sum=3, len=2, 3/2 = 1 (integer division)
val result = average_i64([1, 2])
expect(result).to_equal(1)
```

</details>

### median_i64

#### computes median of odd-length list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = median_i64([3, 1, 2])
expect(result).to_equal(2)
```

</details>

#### computes median of even-length list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# [1, 2, 3, 4] -> (2 + 3) / 2 = 2 (integer division)
val result = median_i64([4, 1, 3, 2])
expect(result).to_equal(2)
```

</details>

#### returns nil for empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = median_i64([])
expect(result).to_be_nil()
```

</details>

#### computes median of single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = median_i64([42])
expect(result).to_equal(42)
```

</details>

#### computes median of sorted list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = median_i64([10, 20, 30, 40, 50])
expect(result).to_equal(30)
```

</details>

#### handles duplicate values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = median_i64([5, 5, 5])
expect(result).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/math_comprehensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Math constants
- math_abs (f64)
- math_abs_i64
- math_min (f64)
- math_max (f64)
- math_min_i64
- math_max_i64
- math_clamp (f64)
- math_clamp_i64
- math_sign (f64)
- math_sign_i64
- math_lerp
- math_is_close
- math_gcd
- math_lcm
- math_pow_i64
- math_factorial
- math_to_radians
- math_to_degrees
- abs_i64 (alias)
- min_i64 (alias)
- max_i64 (alias)
- clamp_i64 (alias)
- sign_i64 (alias)
- pow_i64 (alias)
- gcd (alias)
- lcm (alias)
- factorial (alias)
- binomial
- is_even
- is_odd
- is_divisible_by
- in_range_i64
- sum_i64
- product_i64
- average_i64
- median_i64

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 138 |
| Active scenarios | 138 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
