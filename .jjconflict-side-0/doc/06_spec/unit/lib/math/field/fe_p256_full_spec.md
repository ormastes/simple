# Fe P256 Full Specification

> Tests covering FeP256 axioms — additive identity (a + 0 == a), FeP256 axioms — additive inverse (a + (-a) == 0), FeP256 axioms — associativity, FeP256 axioms — distributivity (a * (b + c) == a*b + a*c), FeP256 edge cases, FeP256 — random fe_add, FeP256 — random fe_sub, FeP256 — random fe_mul, FeP256 — random fe_sq, FeP256 — random fe_inv, FeP256 — fe_cond_select / fe_cond_swap branch coverage, FeP256 — fe_pow.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 55 | 55 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fe P256 Full Specification

## Scenarios

### FeP256 axioms — additive identity (a + 0 == a)

#### fe_add(0, 0) == 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fe_add(0, 0) == 0
   - Expected: fe_is_zero(fe_add(fe_zero(), fe_zero())) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_add(0, 0) == 0")
expect(fe_is_zero(fe_add(fe_zero(), fe_zero()))).to_equal(true)
```

</details>

#### fe_add(1, 0) == 1

- fe_add(1, 0) == 1
   - Expected: fe_eq(fe_add(fe_one(), fe_zero()), fe_one()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_add(1, 0) == 1")
expect(fe_eq(fe_add(fe_one(), fe_zero()), fe_one())).to_equal(true)
```

</details>

#### fe_add(p-1, 0) == p-1

- fe_add(p-1, 0) == p-1
   - Expected: fe_eq(fe_add(a, fe_zero()), a) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_add(p-1, 0) == p-1")
val a = _fe_p_minus_1()
expect(fe_eq(fe_add(a, fe_zero()), a)).to_equal(true)
```

</details>

#### fe_add(random_a, 0) == random_a

- fe_add(random_a, 0) == random_a
   - Expected: fe_eq(fe_add(a, fe_zero()), a) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_add(random_a, 0) == random_a")
val a = _fe_random_a()
expect(fe_eq(fe_add(a, fe_zero()), a)).to_equal(true)
```

</details>

#### fe_add(0, random_b) == random_b

- fe_add(0, random_b) == random_b
   - Expected: fe_eq(fe_add(fe_zero(), b), b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_add(0, random_b) == random_b")
val b = _fe_random_b()
expect(fe_eq(fe_add(fe_zero(), b), b)).to_equal(true)
```

</details>

### FeP256 axioms — additive inverse (a + (-a) == 0)

#### fe_add(1, fe_neg(1)) == 0

- fe_add(1, fe_neg(1)) == 0
   - Expected: fe_is_zero(fe_add(fe_one(), fe_neg(fe_one()))) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_add(1, fe_neg(1)) == 0")
expect(fe_is_zero(fe_add(fe_one(), fe_neg(fe_one())))).to_equal(true)
```

</details>

#### fe_add(p-1, 1) == 0  (since p-1 == -1)

- fe_add(p-1, 1) == 0  (since p-1 == -1)
   - Expected: fe_is_zero(fe_add(_fe_p_minus_1(), fe_one())) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_add(p-1, 1) == 0  (since p-1 == -1)")
expect(fe_is_zero(fe_add(_fe_p_minus_1(), fe_one()))).to_equal(true)
```

</details>

#### fe_neg(0) == 0

- fe_neg(0) == 0
   - Expected: fe_is_zero(fe_neg(fe_zero())) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_neg(0) == 0")
expect(fe_is_zero(fe_neg(fe_zero()))).to_equal(true)
```

</details>

#### fe_add(random_a, fe_neg(random_a)) == 0

- fe_add(random_a, fe_neg(random_a)) == 0
   - Expected: fe_is_zero(fe_add(a, fe_neg(a))) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_add(random_a, fe_neg(random_a)) == 0")
val a = _fe_random_a()
expect(fe_is_zero(fe_add(a, fe_neg(a)))).to_equal(true)
```

</details>

#### fe_sub(random_b, random_b) == 0

- fe_sub(random_b, random_b) == 0
   - Expected: fe_is_zero(fe_sub(b, b)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_sub(random_b, random_b) == 0")
val b = _fe_random_b()
expect(fe_is_zero(fe_sub(b, b))).to_equal(true)
```

</details>

### FeP256 axioms — associativity

#### (1 + 2) + 3 == 1 + (2 + 3)

- (1 + 2) + 3 == 1 + (2 + 3)
   - Expected: fe_eq(left, right) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(1 + 2) + 3 == 1 + (2 + 3)")
val one = fe_one()
val two = _fe_two()
val three = _fe_three()
val left = fe_add(fe_add(one, two), three)
val right = fe_add(one, fe_add(two, three))
expect(fe_eq(left, right)).to_equal(true)
```

</details>

#### (a + b) + c == a + (b + c)  (random)

- (a + b) + c == a + (b + c)  (random)
   - Expected: fe_eq(left, right) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(a + b) + c == a + (b + c)  (random)")
val a = _fe_random_a()
val b = _fe_random_b()
val c = _fe_random_c()
val left = fe_add(fe_add(a, b), c)
val right = fe_add(a, fe_add(b, c))
expect(fe_eq(left, right)).to_equal(true)
```

</details>

#### (2 * 3) * 4 == 2 * (3 * 4)

- (2 * 3) * 4 == 2 * (3 * 4)
   - Expected: fe_eq(left, right) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(2 * 3) * 4 == 2 * (3 * 4)")
val two = _fe_two()
val three = _fe_three()
val four = _fe_from_u64(4)
val left = fe_mul(fe_mul(two, three), four)
val right = fe_mul(two, fe_mul(three, four))
expect(fe_eq(left, right)).to_equal(true)
```

</details>

#### (a * b) * c == a * (b * c)  (random)

- (a * b) * c == a * (b * c)  (random)
   - Expected: fe_eq(left, right) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(a * b) * c == a * (b * c)  (random)")
val a = _fe_random_a()
val b = _fe_random_b()
val c = _fe_random_c()
val left = fe_mul(fe_mul(a, b), c)
val right = fe_mul(a, fe_mul(b, c))
expect(fe_eq(left, right)).to_equal(true)
```

</details>

#### (p-1) * (p-1) is associative-stable

- (p-1) * (p-1) is associative-stable
   - Expected: fe_eq(left, right) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(p-1) * (p-1) is associative-stable")
val pm1 = _fe_p_minus_1()
val left = fe_mul(fe_mul(pm1, pm1), pm1)
val right = fe_mul(pm1, fe_mul(pm1, pm1))
expect(fe_eq(left, right)).to_equal(true)
```

</details>

### FeP256 axioms — distributivity (a * (b + c) == a*b + a*c)

#### 2 * (3 + 5) == 2*3 + 2*5

- 2 * (3 + 5) == 2*3 + 2*5
   - Expected: fe_eq(left, right) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2 * (3 + 5) == 2*3 + 2*5")
val a = _fe_two()
val b = _fe_three()
val c = _fe_from_u64(5)
val left = fe_mul(a, fe_add(b, c))
val right = fe_add(fe_mul(a, b), fe_mul(a, c))
expect(fe_eq(left, right)).to_equal(true)
```

</details>

#### random_a * (random_b + random_c) == random_a*random_b + random_a*random_c

- random_a * (random_b + random_c) == random_a*random_b + random_a*random_c
   - Expected: fe_eq(left, right) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("random_a * (random_b + random_c) == random_a*random_b + random_a*random_c")
val a = _fe_random_a()
val b = _fe_random_b()
val c = _fe_random_c()
val left = fe_mul(a, fe_add(b, c))
val right = fe_add(fe_mul(a, b), fe_mul(a, c))
expect(fe_eq(left, right)).to_equal(true)
```

</details>

#### (p-1) * (1 + 1) == (p-1)*1 + (p-1)*1

- (p-1) * (1 + 1) == (p-1)*1 + (p-1)*1
   - Expected: fe_eq(left, right) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("(p-1) * (1 + 1) == (p-1)*1 + (p-1)*1")
val pm1 = _fe_p_minus_1()
val one = fe_one()
val left = fe_mul(pm1, fe_add(one, one))
val right = fe_add(fe_mul(pm1, one), fe_mul(pm1, one))
expect(fe_eq(left, right)).to_equal(true)
```

</details>

### FeP256 edge cases

#### fe_to_bytes(fe_zero()) == 32 zeros (canonical)

- fe_to_bytes(fe_zero()) == 32 zeros (canonical)
   - Expected: out[0] equals `0x00`
   - Expected: out[31] equals `0x00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_to_bytes(fe_zero()) == 32 zeros (canonical)")
val out = fe_to_bytes(fe_zero())
expect(out[0]).to_equal(0x00)
expect(out[31]).to_equal(0x00)
```

</details>

#### fe_to_bytes(fe_one()) ends with 0x01

- fe_to_bytes(fe_one()) ends with 0x01
   - Expected: out[31] equals `0x01`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_to_bytes(fe_one()) ends with 0x01")
val out = fe_to_bytes(fe_one())
expect(out[31]).to_equal(0x01)
```

</details>

#### fe_to_bytes(p) reduces to 32 zeros (non-canonical zero)

- fe_to_bytes(p) reduces to 32 zeros (non-canonical zero)
   - Expected: out[0] equals `0x00`
   - Expected: out[15] equals `0x00`
   - Expected: out[31] equals `0x00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_to_bytes(p) reduces to 32 zeros (non-canonical zero)")
val out = fe_to_bytes(_fe_p())
expect(out[0]).to_equal(0x00)
expect(out[15]).to_equal(0x00)
expect(out[31]).to_equal(0x00)
```

</details>

#### fe_is_zero(p) == true (canonical zero detection)

- fe_is_zero(p) == true (canonical zero detection)
   - Expected: fe_is_zero(_fe_p()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_is_zero(p) == true (canonical zero detection)")
expect(fe_is_zero(_fe_p())).to_equal(true)
```

</details>

#### fe_to_bytes(p-1) high byte is 0xff, low byte is 0xfe

- fe_to_bytes(p-1) high byte is 0xff, low byte is 0xfe
   - Expected: out[0] equals `0xff`
   - Expected: out[31] equals `0xfe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_to_bytes(p-1) high byte is 0xff, low byte is 0xfe")
val out = fe_to_bytes(_fe_p_minus_1())
expect(out[0]).to_equal(0xff)
expect(out[31]).to_equal(0xfe)
```

</details>

### FeP256 — random fe_add

#### fe_add commutative: a + b == b + a

- fe_add commutative: a + b == b + a
   - Expected: fe_eq(fe_add(a, b), fe_add(b, a)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_add commutative: a + b == b + a")
val a = _fe_random_a()
val b = _fe_random_b()
expect(fe_eq(fe_add(a, b), fe_add(b, a))).to_equal(true)
```

</details>

#### fe_add(random_a, random_a) == 2 * random_a

- fe_add(random_a, random_a) == 2 * random_a
   - Expected: fe_eq(fe_add(a, a), fe_mul(_fe_two(), a)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_add(random_a, random_a) == 2 * random_a")
val a = _fe_random_a()
expect(fe_eq(fe_add(a, a), fe_mul(_fe_two(), a))).to_equal(true)
```

</details>

#### fe_add(p-1, p-1) == p-2

- fe_add(p-1, p-1) == p-2
   - Expected: fe_eq(fe_add(pm1, pm1), pm2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_add(p-1, p-1) == p-2")
val pm1 = _fe_p_minus_1()
val pm2 = fe_sub(pm1, fe_one())
expect(fe_eq(fe_add(pm1, pm1), pm2)).to_equal(true)
```

</details>

#### fe_add(2^32, 2^32) wraps cleanly to 2^33

- fe_add(2^32, 2^32) wraps cleanly to 2^33
   - Expected: fe_eq(fe_add(a, a), expected) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_add(2^32, 2^32) wraps cleanly to 2^33")
val a = _fe_from_u64(0x100000000)
val expected = _fe_from_u64(0x200000000)
expect(fe_eq(fe_add(a, a), expected)).to_equal(true)
```

</details>

#### fe_add(random_a, fe_neg(random_b)) == fe_sub(random_a, random_b)

- fe_add(random_a, fe_neg(random_b)) == fe_sub(random_a, random_b)
   - Expected: fe_eq(fe_add(a, fe_neg(b)), fe_sub(a, b)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_add(random_a, fe_neg(random_b)) == fe_sub(random_a, random_b)")
val a = _fe_random_a()
val b = _fe_random_b()
expect(fe_eq(fe_add(a, fe_neg(b)), fe_sub(a, b))).to_equal(true)
```

</details>

### FeP256 — random fe_sub

#### fe_sub(0, 1) == p-1

- fe_sub(0, 1) == p-1
   - Expected: fe_eq(fe_sub(fe_zero(), fe_one()), _fe_p_minus_1()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_sub(0, 1) == p-1")
expect(fe_eq(fe_sub(fe_zero(), fe_one()), _fe_p_minus_1())).to_equal(true)
```

</details>

#### fe_sub(1, p-1) == 2

- fe_sub(1, p-1) == 2
   - Expected: fe_eq(fe_sub(fe_one(), _fe_p_minus_1()), _fe_two()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_sub(1, p-1) == 2")
expect(fe_eq(fe_sub(fe_one(), _fe_p_minus_1()), _fe_two())).to_equal(true)
```

</details>

#### fe_sub(random_a, random_a) == 0

- fe_sub(random_a, random_a) == 0
   - Expected: fe_is_zero(fe_sub(a, a)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_sub(random_a, random_a) == 0")
val a = _fe_random_a()
expect(fe_is_zero(fe_sub(a, a))).to_equal(true)
```

</details>

#### fe_sub(a, 0) == a

- fe_sub(a, 0) == a
   - Expected: fe_eq(fe_sub(a, fe_zero()), a) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_sub(a, 0) == a")
val a = _fe_random_b()
expect(fe_eq(fe_sub(a, fe_zero()), a)).to_equal(true)
```

</details>

#### fe_sub(a, b) + b == a

- fe_sub(a, b) + b == a
   - Expected: fe_eq(fe_add(fe_sub(a, b), b), a) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_sub(a, b) + b == a")
val a = _fe_random_a()
val b = _fe_random_b()
expect(fe_eq(fe_add(fe_sub(a, b), b), a)).to_equal(true)
```

</details>

### FeP256 — random fe_mul

#### fe_mul commutative: a * b == b * a

- fe_mul commutative: a * b == b * a
   - Expected: fe_eq(fe_mul(a, b), fe_mul(b, a)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_mul commutative: a * b == b * a")
val a = _fe_random_a()
val b = _fe_random_b()
expect(fe_eq(fe_mul(a, b), fe_mul(b, a))).to_equal(true)
```

</details>

#### fe_mul(2, 3) == 6

- fe_mul(2, 3) == 6
   - Expected: fe_eq(fe_mul(_fe_two(), _fe_three()), _fe_six()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_mul(2, 3) == 6")
expect(fe_eq(fe_mul(_fe_two(), _fe_three()), _fe_six())).to_equal(true)
```

</details>

#### fe_mul(p-1, p-1) == 1   (since (-1)^2 == 1)

- fe_mul(p-1, p-1) == 1   (since (-1)^2 == 1)
   - Expected: fe_eq(fe_mul(pm1, pm1), fe_one()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_mul(p-1, p-1) == 1   (since (-1)^2 == 1)")
val pm1 = _fe_p_minus_1()
expect(fe_eq(fe_mul(pm1, pm1), fe_one())).to_equal(true)
```

</details>

#### fe_mul(0xffffffff, 0xffffffff) == 0xfffffffe00000001

- fe_mul(0xffffffff, 0xffffffff) == 0xfffffffe00000001
   - Expected: fe_eq(fe_mul(a, a), expected) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_mul(0xffffffff, 0xffffffff) == 0xfffffffe00000001")
val a = _fe_from_u64(0xffffffff)
val expected = _fe_from_u64(0xfffffffe00000001)
expect(fe_eq(fe_mul(a, a), expected)).to_equal(true)
```

</details>

#### fe_mul(random_a, fe_one()) == random_a

- fe_mul(random_a, fe_one()) == random_a
   - Expected: fe_eq(fe_mul(a, fe_one()), a) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_mul(random_a, fe_one()) == random_a")
val a = _fe_random_a()
expect(fe_eq(fe_mul(a, fe_one()), a)).to_equal(true)
```

</details>

### FeP256 — random fe_sq

#### fe_sq(0) == 0

- fe_sq(0) == 0
   - Expected: fe_is_zero(fe_sq(fe_zero())) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_sq(0) == 0")
expect(fe_is_zero(fe_sq(fe_zero()))).to_equal(true)
```

</details>

#### fe_sq(1) == 1

- fe_sq(1) == 1
   - Expected: fe_eq(fe_sq(fe_one()), fe_one()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_sq(1) == 1")
expect(fe_eq(fe_sq(fe_one()), fe_one())).to_equal(true)
```

</details>

#### fe_sq(2) == 4

- fe_sq(2) == 4
   - Expected: fe_eq(fe_sq(_fe_two()), _fe_from_u64(4)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_sq(2) == 4")
expect(fe_eq(fe_sq(_fe_two()), _fe_from_u64(4))).to_equal(true)
```

</details>

#### fe_sq(p-1) == 1   ((-1)^2 == 1 mod p)

- fe_sq(p-1) == 1   ((-1)^2 == 1 mod p)
   - Expected: fe_eq(fe_sq(_fe_p_minus_1()), fe_one()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_sq(p-1) == 1   ((-1)^2 == 1 mod p)")
expect(fe_eq(fe_sq(_fe_p_minus_1()), fe_one())).to_equal(true)
```

</details>

#### fe_sq(random_a) == fe_mul(random_a, random_a)

- fe_sq(random_a) == fe_mul(random_a, random_a)
   - Expected: fe_eq(fe_sq(a), fe_mul(a, a)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_sq(random_a) == fe_mul(random_a, random_a)")
val a = _fe_random_a()
expect(fe_eq(fe_sq(a), fe_mul(a, a))).to_equal(true)
```

</details>

### FeP256 — random fe_inv

#### fe_inv(1) == 1

- fe_inv(1) == 1
   - Expected: fe_eq(fe_inv(fe_one()), fe_one()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_inv(1) == 1")
expect(fe_eq(fe_inv(fe_one()), fe_one())).to_equal(true)
```

</details>

#### fe_inv(p-1) == p-1   ((-1)^-1 == -1)

- fe_inv(p-1) == p-1   ((-1)^-1 == -1)
   - Expected: fe_eq(fe_inv(pm1), pm1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_inv(p-1) == p-1   ((-1)^-1 == -1)")
val pm1 = _fe_p_minus_1()
expect(fe_eq(fe_inv(pm1), pm1)).to_equal(true)
```

</details>

#### fe_mul(random_a, fe_inv(random_a)) == 1

- fe_mul(random_a, fe_inv(random_a)) == 1
   - Expected: fe_eq(fe_mul(a, fe_inv(a)), fe_one()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_mul(random_a, fe_inv(random_a)) == 1")
val a = _fe_random_a()
expect(fe_eq(fe_mul(a, fe_inv(a)), fe_one())).to_equal(true)
```

</details>

#### fe_inv(fe_inv(random_b)) == random_b

- fe_inv(fe_inv(random_b)) == random_b
   - Expected: fe_eq(fe_inv(fe_inv(b)), b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_inv(fe_inv(random_b)) == random_b")
val b = _fe_random_b()
expect(fe_eq(fe_inv(fe_inv(b)), b)).to_equal(true)
```

</details>

#### fe_mul(2, fe_inv(2)) == 1

- fe_mul(2, fe_inv(2)) == 1
   - Expected: fe_eq(fe_mul(two, fe_inv(two)), fe_one()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_mul(2, fe_inv(2)) == 1")
val two = _fe_two()
expect(fe_eq(fe_mul(two, fe_inv(two)), fe_one())).to_equal(true)
```

</details>

### FeP256 — fe_cond_select / fe_cond_swap branch coverage

#### fe_cond_select(a, b, 0) == a

- fe_cond_select(a, b, 0) == a
   - Expected: fe_eq(fe_cond_select(a, b, 0), a) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_cond_select(a, b, 0) == a")
val a = _fe_random_a()
val b = _fe_random_b()
expect(fe_eq(fe_cond_select(a, b, 0), a)).to_equal(true)
```

</details>

#### fe_cond_select(a, b, 1) == b

- fe_cond_select(a, b, 1) == b
   - Expected: fe_eq(fe_cond_select(a, b, 1), b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_cond_select(a, b, 1) == b")
val a = _fe_random_a()
val b = _fe_random_b()
expect(fe_eq(fe_cond_select(a, b, 1), b)).to_equal(true)
```

</details>

#### fe_cond_swap(a, b, 0) leaves (a, b) unchanged

- fe_cond_swap(a, b, 0) leaves (a, b) unchanged
   - Expected: fe_eq(a2, a) is true
   - Expected: fe_eq(b2, b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_cond_swap(a, b, 0) leaves (a, b) unchanged")
val a = _fe_random_a()
val b = _fe_random_b()
val (a2, b2) = fe_cond_swap(a, b, 0)
expect(fe_eq(a2, a)).to_equal(true)
expect(fe_eq(b2, b)).to_equal(true)
```

</details>

#### fe_cond_swap(a, b, 1) swaps (a, b) -> (b, a)

- fe_cond_swap(a, b, 1) swaps (a, b) -> (b, a)
   - Expected: fe_eq(a2, b) is true
   - Expected: fe_eq(b2, a) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_cond_swap(a, b, 1) swaps (a, b) -> (b, a)")
val a = _fe_random_a()
val b = _fe_random_b()
val (a2, b2) = fe_cond_swap(a, b, 1)
expect(fe_eq(a2, b)).to_equal(true)
expect(fe_eq(b2, a)).to_equal(true)
```

</details>

### FeP256 — fe_pow

#### fe_pow(x, [0]) == 1

- fe_pow(x, [0]) == 1
   - Expected: fe_eq(fe_pow(a, e), fe_one()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_pow(x, [0]) == 1")
val a = _fe_random_a()
val e: [u8] = [0.to_u8()]
expect(fe_eq(fe_pow(a, e), fe_one())).to_equal(true)
```

</details>

#### fe_pow(x, [1]) == x

- fe_pow(x, [1]) == x
   - Expected: fe_eq(fe_pow(a, e), a) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_pow(x, [1]) == x")
val a = _fe_random_a()
val e: [u8] = [1.to_u8()]
expect(fe_eq(fe_pow(a, e), a)).to_equal(true)
```

</details>

#### fe_pow(x, [2]) == fe_sq(x)

- fe_pow(x, [2]) == fe_sq(x)
   - Expected: fe_eq(fe_pow(a, e), fe_sq(a)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_pow(x, [2]) == fe_sq(x)")
val a = _fe_random_b()
val e: [u8] = [2.to_u8()]
expect(fe_eq(fe_pow(a, e), fe_sq(a))).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/math/field/fe_p256_full_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FeP256 axioms — additive identity (a + 0 == a), FeP256 axioms — additive inverse (a + (-a) == 0), FeP256 axioms — associativity, FeP256 axioms — distributivity (a * (b + c) == a*b + a*c), FeP256 edge cases, FeP256 — random fe_add, FeP256 — random fe_sub, FeP256 — random fe_mul, FeP256 — random fe_sq, FeP256 — random fe_inv, FeP256 — fe_cond_select / fe_cond_swap branch coverage, FeP256 — fe_pow.
- FeP256 axioms — additive identity (a + 0 == a)
- FeP256 axioms — additive inverse (a + (-a) == 0)
- FeP256 axioms — associativity
- FeP256 axioms — distributivity (a * (b + c) == a*b + a*c)
- FeP256 edge cases
- FeP256 — random fe_add
- FeP256 — random fe_sub
- FeP256 — random fe_mul
- FeP256 — random fe_sq
- FeP256 — random fe_inv
- FeP256 — fe_cond_select / fe_cond_swap branch coverage
- FeP256 — fe_pow

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

- Canonical SPipe generation for source `659d598df23fa79679eb3ec17ca42714bee3f49d334b23048ef3b74707b134f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `659d598df23fa79679eb3ec17ca42714bee3f49d334b23048ef3b74707b134f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `659d598df23fa79679eb3ec17ca42714bee3f49d334b23048ef3b74707b134f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/math/field/fe_p256_full_spec.spl
mirror: doc/06_spec/unit/lib/math/field/fe_p256_full_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/math/field/fe_p256_full_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/math/field/fe_p256_full_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/math/field/fe_p256_full_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fe_add(0, 0) == 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/math/field/fe_p256_full_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fe_add(1, 0) == 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/math/field/fe_p256_full_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fe_add(p-1, 0) == p-1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
