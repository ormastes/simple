# math_block_solve_spec

> Purpose: inv of 2x2 identity returns ok

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# math_block_solve_spec

Purpose: inv of 2x2 identity returns ok

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/scilib/math_block_solve_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: inv of 2x2 identity returns ok
Audience: compiler and tooling engineers who maintain this spec

## Scenarios

### MathBlock inv — identity input

#### inv of 2x2 identity returns ok

- inv of 2x2 identity returns ok
- Verify: inv of 2x2 identity returns ok
   - Expected: res.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of 2x2 identity returns ok")
step("Verify: inv of 2x2 identity returns ok")
# @req: REQ-FEATURE-MathBlocSolv-001
# identity 2x2: [1,0,0,1]
val a = MbMatrix.new(2, 2, [1.0, 0.0, 0.0, 1.0])
val res = lower_inv(a)
expect(res.is_ok()).to_equal(true)
```

</details>

#### inv of 2x2 identity result rows

- inv of 2x2 identity result rows
- Verify: inv of 2x2 identity result rows
   - Expected: r.matrix.rows equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of 2x2 identity result rows")
step("Verify: inv of 2x2 identity result rows")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 2, [1.0, 0.0, 0.0, 1.0])
val res = lower_inv(a)
val r = res.unwrap()
expect(r.matrix.rows).to_equal(2)  # oracle: value fixed by the spec contract
```

</details>

#### inv of 2x2 identity result cols

- inv of 2x2 identity result cols
- Verify: inv of 2x2 identity result cols
   - Expected: r.matrix.cols equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of 2x2 identity result cols")
step("Verify: inv of 2x2 identity result cols")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 2, [1.0, 0.0, 0.0, 1.0])
val res = lower_inv(a)
val r = res.unwrap()
expect(r.matrix.cols).to_equal(2)  # oracle: value fixed by the spec contract
```

</details>

#### inv of 2x2 identity diagonal [0][0] = 1.0

- inv of 2x2 identity diagonal [0][0] = 1.0
- Verify: inv of 2x2 identity diagonal [0][0] = 1.0
   - Expected: r.matrix.get(0, 0) equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of 2x2 identity diagonal [0][0] = 1.0")
step("Verify: inv of 2x2 identity diagonal [0][0] = 1.0")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 2, [1.0, 0.0, 0.0, 1.0])
val res = lower_inv(a)
val r = res.unwrap()
expect(r.matrix.get(0, 0)).to_equal(1.0)
```

</details>

#### inv of 2x2 identity diagonal [1][1] = 1.0

- inv of 2x2 identity diagonal [1][1] = 1.0
- Verify: inv of 2x2 identity diagonal [1][1] = 1.0
   - Expected: r.matrix.get(1, 1) equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of 2x2 identity diagonal [1][1] = 1.0")
step("Verify: inv of 2x2 identity diagonal [1][1] = 1.0")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 2, [1.0, 0.0, 0.0, 1.0])
val res = lower_inv(a)
val r = res.unwrap()
expect(r.matrix.get(1, 1)).to_equal(1.0)
```

</details>

#### inv of 2x2 identity off-diagonal [0][1] = 0.0

- inv of 2x2 identity off-diagonal [0][1] = 0.0
- Verify: inv of 2x2 identity off-diagonal [0][1] = 0.0
   - Expected: r.matrix.get(0, 1) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of 2x2 identity off-diagonal [0][1] = 0.0")
step("Verify: inv of 2x2 identity off-diagonal [0][1] = 0.0")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 2, [1.0, 0.0, 0.0, 1.0])
val res = lower_inv(a)
val r = res.unwrap()
expect(r.matrix.get(0, 1)).to_equal(0.0)
```

</details>

#### inv of 2x2 identity uses MockLapack provider

- inv of 2x2 identity uses MockLapack provider
- Verify: inv of 2x2 identity uses MockLapack provider
   - Expected: is_lapack is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of 2x2 identity uses MockLapack provider")
step("Verify: inv of 2x2 identity uses MockLapack provider")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 2, [1.0, 0.0, 0.0, 1.0])
val res = lower_inv(a)
val r = res.unwrap()
val is_lapack = r.provider == MathBlockProvider.MockLapack
expect(is_lapack).to_equal(true)
```

</details>

### MathBlock inv — non-trivial 2x2

#### inv of diagonal 2x2 returns ok

- inv of diagonal 2x2 returns ok
- Verify: inv of diagonal 2x2 returns ok
   - Expected: res.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of diagonal 2x2 returns ok")
step("Verify: inv of diagonal 2x2 returns ok")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 2, [2.0, 0.0, 0.0, 4.0])
val res = lower_inv(a)
expect(res.is_ok()).to_equal(true)
```

</details>

#### inv of diagonal 2x2 element [0][0] = 0.5

- inv of diagonal 2x2 element [0][0] = 0.5
- Verify: inv of diagonal 2x2 element [0][0] = 0.5
   - Expected: r.matrix.get(0, 0) equals `0.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of diagonal 2x2 element [0][0] = 0.5")
step("Verify: inv of diagonal 2x2 element [0][0] = 0.5")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 2, [2.0, 0.0, 0.0, 4.0])
val res = lower_inv(a)
val r = res.unwrap()
expect(r.matrix.get(0, 0)).to_equal(0.5)
```

</details>

#### inv of diagonal 2x2 element [1][1] = 0.25

- inv of diagonal 2x2 element [1][1] = 0.25
- Verify: inv of diagonal 2x2 element [1][1] = 0.25
   - Expected: r.matrix.get(1, 1) equals `0.25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of diagonal 2x2 element [1][1] = 0.25")
step("Verify: inv of diagonal 2x2 element [1][1] = 0.25")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 2, [2.0, 0.0, 0.0, 4.0])
val res = lower_inv(a)
val r = res.unwrap()
expect(r.matrix.get(1, 1)).to_equal(0.25)
```

</details>

#### inv of diagonal 2x2 off-diagonal [0][1] = 0.0

- inv of diagonal 2x2 off-diagonal [0][1] = 0.0
- Verify: inv of diagonal 2x2 off-diagonal [0][1] = 0.0
   - Expected: r.matrix.get(0, 1) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of diagonal 2x2 off-diagonal [0][1] = 0.0")
step("Verify: inv of diagonal 2x2 off-diagonal [0][1] = 0.0")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 2, [2.0, 0.0, 0.0, 4.0])
val res = lower_inv(a)
val r = res.unwrap()
expect(r.matrix.get(0, 1)).to_equal(0.0)
```

</details>

### MathBlock inv — error paths

<details>
<summary>Advanced: inv of singular 2x2 zero matrix returns err</summary>

#### inv of singular 2x2 zero matrix returns err

- inv of singular 2x2 zero matrix returns err
- Verify: inv of singular 2x2 zero matrix returns err
   - Expected: res.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of singular 2x2 zero matrix returns err")
step("Verify: inv of singular 2x2 zero matrix returns err")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 2, [0.0, 0.0, 0.0, 0.0])
val res = lower_inv(a)
expect(res.is_ok()).to_equal(false)
```

</details>


</details>

#### inv of singular 2x2 is not ok

- inv of singular 2x2 is not ok
- Verify: inv of singular 2x2 is not ok
   - Expected: ok_check is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of singular 2x2 is not ok")
step("Verify: inv of singular 2x2 is not ok")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 2, [0.0, 0.0, 0.0, 0.0])
val res = lower_inv(a)
val ok_check = res.is_ok()
expect(ok_check).to_equal(false)
```

</details>

<details>
<summary>Advanced: inv of non-square matrix returns err</summary>

#### inv of non-square matrix returns err

- inv of non-square matrix returns err
- Verify: inv of non-square matrix returns err
   - Expected: res.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of non-square matrix returns err")
step("Verify: inv of non-square matrix returns err")
# @req: REQ-FEATURE-MathBlocSolv-001
# 2×3 matrix is not invertible
val a = MbMatrix.new(2, 3, [1.0, 0.0, 0.0, 0.0, 1.0, 0.0])
val res = lower_inv(a)
expect(res.is_ok()).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: inv of non-square matrix error is NonSquare</summary>

#### inv of non-square matrix error is NonSquare

- inv of non-square matrix error is NonSquare
- Verify: inv of non-square matrix error is NonSquare
   - Expected: is_nonsquare is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of non-square matrix error is NonSquare")
step("Verify: inv of non-square matrix error is NonSquare")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 3, [1.0, 0.0, 0.0, 0.0, 1.0, 0.0])
val res = lower_inv(a)
val e = res.unwrap_err()
val is_nonsquare = e == MathBlockError.NonSquare
expect(is_nonsquare).to_equal(true)
```

</details>


</details>

#### inv of 1x1 scalar returns ok

- inv of 1x1 scalar returns ok
- Verify: inv of 1x1 scalar returns ok
   - Expected: res.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of 1x1 scalar returns ok")
step("Verify: inv of 1x1 scalar returns ok")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(1, 1, [4.0])
val res = lower_inv(a)
expect(res.is_ok()).to_equal(true)
```

</details>

#### inv of 1x1 scalar result = 0.25

- inv of 1x1 scalar result = 0.25
- Verify: inv of 1x1 scalar result = 0.25
   - Expected: r.matrix.get(0, 0) equals `0.25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of 1x1 scalar result = 0.25")
step("Verify: inv of 1x1 scalar result = 0.25")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(1, 1, [4.0])
val res = lower_inv(a)
val r = res.unwrap()
expect(r.matrix.get(0, 0)).to_equal(0.25)
```

</details>

#### inv of 1x1 zero is Singular

- inv of 1x1 zero is Singular
- Verify: inv of 1x1 zero is Singular
   - Expected: res.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inv of 1x1 zero is Singular")
step("Verify: inv of 1x1 zero is Singular")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(1, 1, [0.0])
val res = lower_inv(a)
expect(res.is_ok()).to_equal(false)
```

</details>

### MathBlock solve — identity matrix

#### solve identity system 2x2 returns ok

- solve identity system 2x2 returns ok
- Verify: solve identity system 2x2 returns ok
   - Expected: res.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("solve identity system 2x2 returns ok")
step("Verify: solve identity system 2x2 returns ok")
# @req: REQ-FEATURE-MathBlocSolv-001
# identity 2x2: [1,0,0,1]
val a = MbMatrix.new(2, 2, [1.0, 0.0, 0.0, 1.0])
val b = [3.0, 7.0]
val res = lower_solve(a, b)
expect(res.is_ok()).to_equal(true)
```

</details>

#### solve identity system result length

- solve identity system result length
- Verify: solve identity system result length
   - Expected: r.matrix.rows equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("solve identity system result length")
step("Verify: solve identity system result length")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 2, [1.0, 0.0, 0.0, 1.0])
val b = [3.0, 7.0]
val res = lower_solve(a, b)
val r = res.unwrap()
expect(r.matrix.rows).to_equal(2)  # oracle: value fixed by the spec contract
```

</details>

#### solve identity system x[0] = b[0]

- solve identity system x[0] = b[0]
- Verify: solve identity system x[0] = b[0]
   - Expected: r.matrix.get(0, 0) equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("solve identity system x[0] = b[0]")
step("Verify: solve identity system x[0] = b[0]")
# @req: REQ-FEATURE-MathBlocSolv-001
# Cramer: x[0] = (b[0]*a11 - b[1]*a01)/det = (3*1 - 7*0)/1 = 3.0
val a = MbMatrix.new(2, 2, [1.0, 0.0, 0.0, 1.0])
val b = [3.0, 7.0]
val res = lower_solve(a, b)
val r = res.unwrap()
expect(r.matrix.get(0, 0)).to_equal(3.0)
```

</details>

#### solve identity system x[1] = b[1]

- solve identity system x[1] = b[1]
- Verify: solve identity system x[1] = b[1]
   - Expected: r.matrix.get(1, 0) equals `7.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("solve identity system x[1] = b[1]")
step("Verify: solve identity system x[1] = b[1]")
# @req: REQ-FEATURE-MathBlocSolv-001
# Cramer: x[1] = (a00*b[1] - a10*b[0])/det = (1*7 - 0*3)/1 = 7.0
val a = MbMatrix.new(2, 2, [1.0, 0.0, 0.0, 1.0])
val b = [3.0, 7.0]
val res = lower_solve(a, b)
val r = res.unwrap()
expect(r.matrix.get(1, 0)).to_equal(7.0)
```

</details>

#### solve identity system uses MockLapack provider

- solve identity system uses MockLapack provider
- Verify: solve identity system uses MockLapack provider
   - Expected: is_lapack is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("solve identity system uses MockLapack provider")
step("Verify: solve identity system uses MockLapack provider")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 2, [1.0, 0.0, 0.0, 1.0])
val b = [3.0, 7.0]
val res = lower_solve(a, b)
val r = res.unwrap()
val is_lapack = r.provider == MathBlockProvider.MockLapack
expect(is_lapack).to_equal(true)
```

</details>

### MathBlock solve — non-trivial 2x2

#### solve non-trivial 2x2 returns ok

- solve non-trivial 2x2 returns ok
- Verify: solve non-trivial 2x2 returns ok
   - Expected: res.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("solve non-trivial 2x2 returns ok")
step("Verify: solve non-trivial 2x2 returns ok")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 2, [2.0, 1.0, 1.0, 3.0])
val b = [5.0, 10.0]
val res = lower_solve(a, b)
expect(res.is_ok()).to_equal(true)
```

</details>

#### solve non-trivial 2x2 x[0] = 1.0

- solve non-trivial 2x2 x[0] = 1.0
- Verify: solve non-trivial 2x2 x[0] = 1.0
   - Expected: r.matrix.get(0, 0) equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("solve non-trivial 2x2 x[0] = 1.0")
step("Verify: solve non-trivial 2x2 x[0] = 1.0")
# @req: REQ-FEATURE-MathBlocSolv-001
# (5*3 - 10*1)/5 = (15-10)/5 = 1.0
val a = MbMatrix.new(2, 2, [2.0, 1.0, 1.0, 3.0])
val b = [5.0, 10.0]
val res = lower_solve(a, b)
val r = res.unwrap()
expect(r.matrix.get(0, 0)).to_equal(1.0)
```

</details>

#### solve non-trivial 2x2 x[1] = 3.0

- solve non-trivial 2x2 x[1] = 3.0
- Verify: solve non-trivial 2x2 x[1] = 3.0
   - Expected: r.matrix.get(1, 0) equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("solve non-trivial 2x2 x[1] = 3.0")
step("Verify: solve non-trivial 2x2 x[1] = 3.0")
# @req: REQ-FEATURE-MathBlocSolv-001
# (2*10 - 1*5)/5 = (20-5)/5 = 3.0
val a = MbMatrix.new(2, 2, [2.0, 1.0, 1.0, 3.0])
val b = [5.0, 10.0]
val res = lower_solve(a, b)
val r = res.unwrap()
expect(r.matrix.get(1, 0)).to_equal(3.0)
```

</details>

### MathBlock solve — error paths

#### solve singular system returns err

- solve singular system returns err
- Verify: solve singular system returns err
   - Expected: res.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("solve singular system returns err")
step("Verify: solve singular system returns err")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 2, [0.0, 0.0, 0.0, 0.0])
val b = [1.0, 2.0]
val res = lower_solve(a, b)
expect(res.is_ok()).to_equal(false)
```

</details>

#### solve singular system is not ok

- solve singular system is not ok
- Verify: solve singular system is not ok
   - Expected: ok_check is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("solve singular system is not ok")
step("Verify: solve singular system is not ok")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 2, [0.0, 0.0, 0.0, 0.0])
val b = [1.0, 2.0]
val res = lower_solve(a, b)
val ok_check = res.is_ok()
expect(ok_check).to_equal(false)
```

</details>

#### solve non-square system returns err

- solve non-square system returns err
- Verify: solve non-square system returns err
   - Expected: res.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("solve non-square system returns err")
step("Verify: solve non-square system returns err")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(2, 3, [1.0, 0.0, 0.0, 0.0, 1.0, 0.0])
val b = [1.0, 2.0]
val res = lower_solve(a, b)
expect(res.is_ok()).to_equal(false)
```

</details>

#### solve dimension mismatch returns err

- solve dimension mismatch returns err
- Verify: solve dimension mismatch returns err
   - Expected: res.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("solve dimension mismatch returns err")
step("Verify: solve dimension mismatch returns err")
# @req: REQ-FEATURE-MathBlocSolv-001
# A is 2×2 but b has 3 elements
val a = MbMatrix.identity(2)
val b = [1.0, 2.0, 3.0]
val res = lower_solve(a, b)
expect(res.is_ok()).to_equal(false)
```

</details>

### MathBlock scalar fallback — 1x1 matmul

#### 1x1 matmul returns ok

- 1x1 matmul returns ok
- Verify: 1x1 matmul returns ok
   - Expected: res.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("1x1 matmul returns ok")
step("Verify: 1x1 matmul returns ok")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(1, 1, [3.0])
val b = MbMatrix.new(1, 1, [4.0])
val res = lower_matmul(a, b)
expect(res.is_ok()).to_equal(true)
```

</details>

#### 1x1 matmul result = 12.0

- 1x1 matmul result = 12.0
- Verify: 1x1 matmul result = 12.0
   - Expected: r.matrix.get(0, 0) equals `12.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("1x1 matmul result = 12.0")
step("Verify: 1x1 matmul result = 12.0")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(1, 1, [3.0])
val b = MbMatrix.new(1, 1, [4.0])
val res = lower_matmul(a, b)
val r = res.unwrap()
expect(r.matrix.get(0, 0)).to_equal(12.0)
```

</details>

#### 1x1 matmul uses Scalar provider

- 1x1 matmul uses Scalar provider
- Verify: 1x1 matmul uses Scalar provider
   - Expected: is_scalar is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("1x1 matmul uses Scalar provider")
step("Verify: 1x1 matmul uses Scalar provider")
# @req: REQ-FEATURE-MathBlocSolv-001
val a = MbMatrix.new(1, 1, [3.0])
val b = MbMatrix.new(1, 1, [4.0])
val res = lower_matmul(a, b)
val r = res.unwrap()
val is_scalar = r.provider == MathBlockProvider.Scalar
expect(is_scalar).to_equal(true)
```

</details>

### MathBlock unsupported form — typed diagnostic

#### unsupported form returns err

- unsupported form returns err
- Verify: unsupported form returns err
   - Expected: res.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unsupported form returns err")
step("Verify: unsupported form returns err")
# @req: REQ-FEATURE-MathBlocSolv-001
val res = lower_unsupported("df_groupby")
expect(res.is_ok()).to_equal(false)
```

</details>

#### unsupported form error is UnsupportedForm

- unsupported form error is UnsupportedForm
- Verify: unsupported form error is UnsupportedForm
   - Expected: is_unsupported is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unsupported form error is UnsupportedForm")
step("Verify: unsupported form error is UnsupportedForm")
# @req: REQ-FEATURE-MathBlocSolv-001
val res = lower_unsupported("df_groupby")
val e = res.unwrap_err()
val is_unsupported = e == MathBlockError.UnsupportedForm
expect(is_unsupported).to_equal(true)
```

</details>

#### classify_op unknown tag is Unsupported

- classify_op unknown tag is Unsupported
- Verify: classify_op unknown tag is Unsupported
   - Expected: is_unsupported is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classify_op unknown tag is Unsupported")
step("Verify: classify_op unknown tag is Unsupported")
# @req: REQ-FEATURE-MathBlocSolv-001
val op = classify_op("df_groupby")
val is_unsupported = op == MathBlockOp.Unsupported
expect(is_unsupported).to_equal(true)
```

</details>

### MathBlock classify_op — op discriminant routing

#### classify matmul

- classify matmul
- Verify: classify matmul
   - Expected: is_matmul is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classify matmul")
step("Verify: classify matmul")
# @req: REQ-FEATURE-MathBlocSolv-001
val op = classify_op("matmul")
val is_matmul = op == MathBlockOp.MatMul
expect(is_matmul).to_equal(true)
```

</details>

#### classify inv

- classify inv
- Verify: classify inv
   - Expected: is_inv is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classify inv")
step("Verify: classify inv")
# @req: REQ-FEATURE-MathBlocSolv-001
val op = classify_op("inv")
val is_inv = op == MathBlockOp.Inv
expect(is_inv).to_equal(true)
```

</details>

#### classify solve

- classify solve
- Verify: classify solve
   - Expected: is_solve is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classify solve")
step("Verify: classify solve")
# @req: REQ-FEATURE-MathBlocSolv-001
val op = classify_op("solve")
val is_solve = op == MathBlockOp.Solve
expect(is_solve).to_equal(true)
```

</details>

#### classify scalar_mul

- classify scalar_mul
- Verify: classify scalar_mul
   - Expected: is_scalar_mul is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classify scalar_mul")
step("Verify: classify scalar_mul")
# @req: REQ-FEATURE-MathBlocSolv-001
val op = classify_op("scalar_mul")
val is_scalar_mul = op == MathBlockOp.ScalarMul
expect(is_scalar_mul).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-FEATURE-MathBlocSolv-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `414bd6ab1701ab40a6b8490d786672ffe178fc7639e9d4f1dde4213e9f24d4a8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `414bd6ab1701ab40a6b8490d786672ffe178fc7639e9d4f1dde4213e9f24d4a8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `414bd6ab1701ab40a6b8490d786672ffe178fc7639e9d4f1dde4213e9f24d4a8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/scilib/math_block_solve_spec.spl
mirror: doc/06_spec/03_system/feature/scilib/math_block_solve_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/scilib/math_block_solve_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/scilib/math_block_solve_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/scilib/math_block_solve_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/scilib/math_block_solve_spec.spl:240:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inv of 2x2 identity returns ok' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/scilib/math_block_solve_spec.spl:250:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inv of 2x2 identity result rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/scilib/math_block_solve_spec.spl:260:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inv of 2x2 identity result cols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
