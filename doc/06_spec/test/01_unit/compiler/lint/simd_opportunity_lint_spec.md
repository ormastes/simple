# simd_opportunity_lint_spec

> Detects `for i in 0..n: out[i] = a[i] + b[i]` and suggests FixedVec.add.

<!-- sdn-diagram:id=simd_opportunity_lint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simd_opportunity_lint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simd_opportunity_lint_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simd_opportunity_lint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 70 | 70 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simd_opportunity_lint_spec

Detects `for i in 0..n: out[i] = a[i] + b[i]` and suggests FixedVec.add.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/simd_opportunity_lint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Element-wise Add Detection

    Detects `for i in 0..n: out[i] = a[i] + b[i]` and suggests FixedVec.add.

## Scenarios

### L-SIMD-001: element-wise add loop

#### when loop body is pure element-wise add

#### fires on out[i] = a[i] + b[i] pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn process(a: [i32], b: [i32], n: i64):\n    var out: [i32] = []\n    for i in 0..n:\n        out[i] = a[i] + b[i]\n"
val warnings = lint_simd_elementwise_add(source, "test.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-001")
expect(warnings[0].severity).to_equal("info")
```

</details>

#### includes concrete fix snippet referencing fixedvec_from_slice and .add

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn process(a: [i32], b: [i32], n: i64):\n    for i in 0..n:\n        out[i] = a[i] + b[i]\n"
val warnings = lint_simd_elementwise_add(source, "test.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].fix).to_contain("fixedvec_from_slice")
expect(warnings[0].fix).to_contain(".add(")
expect(warnings[0].hint).to_contain("ScalableVec.add")
```

</details>

#### reports the correct line number

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn process():\n    val x = 1\n    for i in 0..8:\n        out[i] = a[i] + b[i]\n"
val warnings = lint_simd_elementwise_add(source, "test.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].line_num).to_equal(3)
```

</details>

<details>
<summary>Advanced: uses FixedVec-only wording for literal fixed-width loop bounds</summary>

#### uses FixedVec-only wording for literal fixed-width loop bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn process(a: [i32], b: [i32]):\n    for i in 0..8:\n        out[i] = a[i] + b[i]\n"
val warnings = lint_simd_elementwise_add(source, "fixed.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].hint.contains("ScalableVec")).to_equal(false)
expect(warnings[0].fix.contains("ScalableVec")).to_equal(false)
```

</details>


</details>

#### negative cases: loop body has unsafe patterns

#### does not fire when body contains a function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn process():\n    for i in 0..n:\n        out[i] = transform(a[i]) + b[i]\n"
val warnings = lint_simd_elementwise_add(source, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

<details>
<summary>Advanced: does not fire when loop already uses FixedVec</summary>

#### does not fire when loop already uses FixedVec

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn process():\n    for i in 0..n:\n        val v = FixedVec<i32>(elements: a, lanes: 4)\n        out[i] = a[i] + b[i]\n"
val warnings = lint_simd_elementwise_add(source, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>


</details>

### L-SIMD-002: scalar accumulator reduce_sum

#### when accumulator pattern is present

<details>
<summary>Advanced: fires on var s = 0 followed by accumulator loop</summary>

#### fires on var s = 0 followed by accumulator loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sum_array(a: [i32], n: i64) -> i64:\n    var s = 0\n    for i in 0..n:\n        s = s + a[i]\n    s\n"
val warnings = lint_simd_reduce_sum(source, "test.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-002")
expect(warnings[0].severity).to_equal("info")
```

</details>


</details>

#### includes reduce_sum in the fix snippet

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sum_array(a: [i32], n: i64) -> i64:\n    var total = 0\n    for i in 0..n:\n        total = total + a[i]\n    total\n"
val warnings = lint_simd_reduce_sum(source, "total.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].fix).to_contain("reduce_sum")
```

</details>

#### negative cases

<details>
<summary>Advanced: does not fire when loop body has a function call</summary>

#### does not fire when loop body has a function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sum_array(a: [i32], n: i64) -> i64:\n    var s = 0\n    for i in 0..n:\n        s = s + compute(a[i])\n    s\n"
val warnings = lint_simd_reduce_sum(source, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>


</details>

### L-SIMD-003: byte-array XOR loop

#### when XOR pattern is present

#### fires on out[i] = a[i] ^ b[i] pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn xor_encrypt(a: [u8], b: [u8], n: i64):\n    var out: [u8] = []\n    for i in 0..n:\n        out[i] = a[i] ^ b[i]\n"
val warnings = lint_simd_xor_loop(source, "cipher.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-003")
```

</details>

#### fires as warning severity (not info)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn xor_encrypt(a: [u8], b: [u8], n: i64):\n    for i in 0..n:\n        out[i] = a[i] ^ b[i]\n"
val warnings = lint_simd_xor_loop(source, "cipher.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].severity).to_equal("warning")
```

</details>

#### fix snippet references FixedVec xor method

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn xor_encrypt(a: [u8], b: [u8], n: i64):\n    for i in 0..n:\n        out[i] = a[i] ^ b[i]\n"
val warnings = lint_simd_xor_loop(source, "cipher.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].fix).to_contain(".xor(")
```

</details>

#### negative cases

#### does not fire when body contains I/O

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn xor_and_write(a: [u8], b: [u8], n: i64):\n    for i in 0..n:\n        out[i] = a[i] ^ b[i]\n        print out[i]\n"
val warnings = lint_simd_xor_loop(source, "cipher.spl")
expect(warnings.len()).to_equal(0)
```

</details>

<details>
<summary>Advanced: does not fire when loop uses FFI rt_ call</summary>

#### does not fire when loop uses FFI rt_ call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn xor_ffi(a: [u8], b: [u8], n: i64):\n    for i in 0..n:\n        out[i] = a[i] ^ b[i]\n        rt_mem_barrier()\n"
val warnings = lint_simd_xor_loop(source, "cipher.spl")
expect(warnings.len()).to_equal(0)
```

</details>


</details>

### L-SIMD-004: element-wise max loop

#### when max call pattern is present

#### fires on out[i] = max(a[i], b[i]) pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn elemwise_max(a: [f32], b: [f32], n: i64):\n    for i in 0..n:\n        out[i] = max(a[i], b[i])\n"
val warnings = lint_simd_elementwise_max(source, "math.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-004")
expect(warnings[0].severity).to_equal("info")
```

</details>

#### fix snippet references FixedVec.max

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn elemwise_max(a: [f32], b: [f32], n: i64):\n    for i in 0..n:\n        out[i] = max(a[i], b[i])\n"
val warnings = lint_simd_elementwise_max(source, "math.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].fix).to_contain(".max(")
```

</details>

#### negative cases

#### does not fire when body contains a non-array function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn process(a: [f32], b: [f32], n: i64):\n    for i in 0..n:\n        out[i] = max(transform(a[i]), b[i])\n"
val warnings = lint_simd_elementwise_max(source, "math.spl")
expect(warnings.len()).to_equal(0)
```

</details>

### L-SIMD-005: constant right-shift loop

#### when constant shr pattern is present

#### fires on out[i] = a[i] >> K pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn shift_right(a: [i32], n: i64):\n    for i in 0..n:\n        out[i] = a[i] >> 2\n"
val warnings = lint_simd_const_shr_loop(source, "bits.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-005")
```

</details>

#### fires as note severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn shift_right(a: [i32], n: i64):\n    for i in 0..n:\n        out[i] = a[i] >> 4\n"
val warnings = lint_simd_const_shr_loop(source, "bits.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].severity).to_equal("note")
```

</details>

#### fix snippet references shr_logical

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn shift_right(a: [i32], n: i64):\n    for i in 0..n:\n        out[i] = a[i] >> 3\n"
val warnings = lint_simd_const_shr_loop(source, "bits.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].fix).to_contain("shr_logical")
```

</details>

#### negative cases

<details>
<summary>Advanced: does not fire when loop body has a function call</summary>

#### does not fire when loop body has a function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn shift_right(a: [i32], n: i64):\n    for i in 0..n:\n        out[i] = normalize(a[i]) >> 2\n"
val warnings = lint_simd_const_shr_loop(source, "bits.spl")
expect(warnings.len()).to_equal(0)
```

</details>


</details>

### lint_simd_opportunities composite runner

#### returns warnings from multiple rules when source has multiple patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn multi(a: [i32], b: [i32], n: i64):\n    for i in 0..n:\n        out[i] = a[i] + b[i]\n    var s = 0\n    for j in 0..n:\n        s = s + a[j]\n"
val warnings = lint_simd_opportunities(source, "multi.spl")
expect(warnings.len()).to_be_greater_than(1)
```

</details>

<details>
<summary>Advanced: returns empty for source with no vectorisable loops</summary>

#### returns empty for source with no vectorisable loops

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn process(a: [i32], n: i64):\n    for i in 0..n:\n        out[i] = transform(a[i])\n"
val warnings = lint_simd_opportunities(source, "clean.spl")
expect(warnings.len()).to_equal(0)
```

</details>


</details>

### SimdOpportunityWarning formatting

#### fmt() includes code, severity, file_path and line_num

1. fix: "val out = fixedvec from slice


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = SimdOpportunityWarning(
    code: "L-SIMD-001",
    severity: "info",
    message: "test message",
    hint: "test hint",
    fix: "val out = fixedvec_from_slice(a).add(fixedvec_from_slice(b)).to_array()",
    line_num: 42,
    file_path: "foo.spl"
)
val output = w.fmt()
expect(output).to_contain("L-SIMD-001")
expect(output).to_contain("info")
expect(output).to_contain("foo.spl")
expect(output).to_contain("42")
```

</details>

#### fmt_with_fix() includes fix snippet

1. fix: "val out = fixedvec from slice


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = SimdOpportunityWarning(
    code: "L-SIMD-003",
    severity: "warning",
    message: "xor loop",
    hint: "use FixedVec.xor",
    fix: "val out = fixedvec_from_slice(a).xor(fixedvec_from_slice(b)).to_array()",
    line_num: 10,
    file_path: "cipher.spl"
)
val output = w.fmt_with_fix()
expect(output).to_contain("xor")
expect(output).to_contain("fixedvec_from_slice")
```

</details>

### L-SIMD-006: memcpy loop

#### when loop body is a pure element copy

#### fires on out[i] = src[i] pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn copy_buf(src: [u8], n: i64):\n    var out: [u8] = []\n    for i in 0..n:\n        out[i] = src[i]\n"
val warnings = lint_simd_memcpy_loop(source, "copy.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-006")
expect(warnings[0].severity).to_equal("warning")
```

</details>

#### fix snippet references fixedvec_from_slice and to_array

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn copy_buf(src: [u8], n: i64):\n    for i in 0..n:\n        out[i] = src[i]\n"
val warnings = lint_simd_memcpy_loop(source, "copy.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].fix).to_contain("fixedvec_from_slice")
expect(warnings[0].fix).to_contain("to_array")
```

</details>

#### negative cases

#### does not fire when body has arithmetic operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn transform(src: [u8], n: i64):\n    for i in 0..n:\n        out[i] = src[i] + 1\n"
val warnings = lint_simd_memcpy_loop(source, "copy.spl")
expect(warnings.len()).to_equal(0)
```

</details>

#### does not fire when body has a function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn transform(src: [u8], n: i64):\n    for i in 0..n:\n        out[i] = convert(src[i])\n"
val warnings = lint_simd_memcpy_loop(source, "copy.spl")
expect(warnings.len()).to_equal(0)
```

</details>

### L-SIMD-007: byte-mismatch scan

#### when mismatch-break pattern is present

#### fires on if a[i] != b[i]: break pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn compare(a: [u8], b: [u8], n: i64) -> bool:\n    for i in 0..n:\n        if a[i] != b[i]: break\n    true\n"
val warnings = lint_simd_byte_mismatch_scan(source, "match.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-007")
expect(warnings[0].severity).to_equal("info")
```

</details>

#### fix snippet references cmp_eq and reduce_and

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn compare(a: [u8], b: [u8], n: i64) -> bool:\n    for i in 0..n:\n        if a[i] != b[i]: break\n    true\n"
val warnings = lint_simd_byte_mismatch_scan(source, "match.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].fix).to_contain("cmp_eq")
expect(warnings[0].fix).to_contain("reduce_and")
```

</details>

#### negative cases

#### does not fire when body has a function call (non-trivial condition)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn compare(a: [u8], b: [u8], n: i64):\n    for i in 0..n:\n        if transform(a[i]) != b[i]: break\n"
val warnings = lint_simd_byte_mismatch_scan(source, "match.spl")
expect(warnings.len()).to_equal(0)
```

</details>

<details>
<summary>Advanced: does not fire when loop already uses FixedVec</summary>

#### does not fire when loop already uses FixedVec

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn compare(a: [u8], b: [u8], n: i64):\n    for i in 0..n:\n        val v = FixedVec<u8>(elements: a, lanes: 16)\n        if a[i] != b[i]: break\n"
val warnings = lint_simd_byte_mismatch_scan(source, "match.spl")
expect(warnings.len()).to_equal(0)
```

</details>


</details>

### L-SIMD-008: ASCII tolower loop

#### when ASCII tolower pattern is present

#### fires on hex range 0x41..0x5A with +32 body

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn tolower(a: [u8], n: i64):\n    for i in 0..n:\n        if a[i] >= 0x41 and a[i] <= 0x5A:\n            out[i] = a[i] + 32\n"
val warnings = lint_simd_ascii_tolower(source, "text.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-008")
expect(warnings[0].severity).to_equal("warning")
```

</details>

#### fires on decimal range 65..90 with +32 body

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn tolower(a: [u8], n: i64):\n    for i in 0..n:\n        if a[i] >= 65 and a[i] <= 90:\n            out[i] = a[i] + 32\n"
val warnings = lint_simd_ascii_tolower(source, "text.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].fix).to_contain("mask_select")
```

</details>

#### negative cases

#### does not fire when range uses function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn tolower(a: [u8], n: i64):\n    for i in 0..n:\n        if is_upper(a[i]):\n            out[i] = a[i] + 32\n"
val warnings = lint_simd_ascii_tolower(source, "text.spl")
expect(warnings.len()).to_equal(0)
```

</details>

<details>
<summary>Advanced: does not fire when loop already uses FixedVec</summary>

#### does not fire when loop already uses FixedVec

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn tolower(a: [u8], n: i64):\n    for i in 0..n:\n        val v = FixedVec<u8>(elements: a, lanes: 16)\n        if a[i] >= 65 and a[i] <= 90:\n            out[i] = a[i] + 32\n"
val warnings = lint_simd_ascii_tolower(source, "text.spl")
expect(warnings.len()).to_equal(0)
```

</details>


</details>

### L-SIMD-009: ReLU max(a[i], 0) loop

#### when ReLU pattern is present

#### fires on out[i] = max(a[i], 0) pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn relu(a: [f32], n: i64):\n    for i in 0..n:\n        out[i] = max(a[i], 0)\n"
val warnings = lint_simd_relu(source, "ml.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-009")
expect(warnings[0].severity).to_equal("info")
```

</details>

#### fix snippet references FixedVec.max with zero vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn relu(a: [f32], n: i64):\n    for i in 0..n:\n        out[i] = max(a[i], 0.0)\n"
val warnings = lint_simd_relu(source, "ml.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].fix).to_contain(".max(")
expect(warnings[0].fix).to_contain("zeros")
```

</details>

#### negative cases

#### does not fire when max has non-zero second argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn clamp(a: [f32], n: i64):\n    for i in 0..n:\n        out[i] = max(a[i], 1.0)\n"
val warnings = lint_simd_relu(source, "ml.spl")
expect(warnings.len()).to_equal(0)
```

</details>

<details>
<summary>Advanced: does not fire when loop body has a function call</summary>

#### does not fire when loop body has a function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn relu(a: [f32], n: i64):\n    for i in 0..n:\n        out[i] = max(scale(a[i]), 0)\n"
val warnings = lint_simd_relu(source, "ml.spl")
expect(warnings.len()).to_equal(0)
```

</details>


</details>

### L-SIMD-010: byte-frequency histogram

#### when plain byte-histogram pattern is present

#### fires on histogram[a[i]] += 1 pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn build_freq(a: [u8], n: i64):\n    var histogram: [i64] = splat_array(0, 256)\n    for i in 0..n:\n        histogram[a[i]] += 1\n"
val warnings = lint_simd_histogram(source, "compress.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-010")
expect(warnings[0].severity).to_equal("note")
```

</details>

#### fix snippet mentions profiling caveat

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn build_freq(a: [u8], n: i64):\n    for i in 0..n:\n        histogram[a[i]] += 1\n"
val warnings = lint_simd_histogram(source, "compress.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].fix).to_contain("profiling")
```

</details>

#### negative cases: non-byte indices

#### does not fire when index uses a function call (e.g., hash(a[i]))

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn build_freq(a: [u8], n: i64):\n    for i in 0..n:\n        histogram[hash(a[i])] += 1\n"
val warnings = lint_simd_histogram(source, "compress.spl")
expect(warnings.len()).to_equal(0)
```

</details>

<details>
<summary>Advanced: does not fire when loop body has FFI call</summary>

#### does not fire when loop body has FFI call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn build_freq(a: [u8], n: i64):\n    for i in 0..n:\n        histogram[a[i]] += 1\n        rt_mem_barrier()\n"
val warnings = lint_simd_histogram(source, "compress.spl")
expect(warnings.len()).to_equal(0)
```

</details>


</details>

### L-SIMD-011: key-XOR cipher loop

#### when key-XOR cipher pattern is present

#### fires on out[i] = a[i] ^ key[i % keylen] pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn encrypt(a: [u8], key: [u8], n: i64, keylen: i64):\n    var out: [u8] = []\n    for i in 0..n:\n        out[i] = a[i] ^ key[i % keylen]\n"
val warnings = lint_simd_key_xor(source, "cipher.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-011")
expect(warnings[0].severity).to_equal("warning")
```

</details>

#### fix snippet references tiling and FixedVec.xor

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn encrypt(a: [u8], key: [u8], n: i64, keylen: i64):\n    for i in 0..n:\n        out[i] = a[i] ^ key[i % keylen]\n"
val warnings = lint_simd_key_xor(source, "cipher.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].fix).to_contain(".xor(")
expect(warnings[0].fix).to_contain("tiled")
```

</details>

#### negative cases

#### does not fire on same-index XOR (a[i] ^ b[i]) — that is L-SIMD-003

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn xor_buf(a: [u8], b: [u8], n: i64):\n    for i in 0..n:\n        out[i] = a[i] ^ b[i]\n"
val warnings = lint_simd_key_xor(source, "cipher.spl")
expect(warnings.len()).to_equal(0)
```

</details>

<details>
<summary>Advanced: does not fire when loop has I/O call</summary>

#### does not fire when loop has I/O call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn encrypt(a: [u8], key: [u8], n: i64, keylen: i64):\n    for i in 0..n:\n        out[i] = a[i] ^ key[i % keylen]\n        print out[i]\n"
val warnings = lint_simd_key_xor(source, "cipher.spl")
expect(warnings.len()).to_equal(0)
```

</details>


</details>

### Bug1: while i < n loop shape — L-SIMD-001

#### positive: while loop fires element-wise add

#### fires on while i < n: out[i] = a[i] + b[i]

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn process(a: [i32], b: [i32], n: i64):\n    var i = 0\n    while i < n:\n        out[i] = a[i] + b[i]\n        i = i + 1\n"
val warnings = lint_simd_elementwise_add(source, "test.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-001")
```

</details>

#### fires on while i < len: out[i] = a[i] + b[i]

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn process(a: [i32], b: [i32]):\n    var i = 0\n    while i < a.len():\n        out[i] = a[i] + b[i]\n        i = i + 1\n"
val warnings = lint_simd_elementwise_add(source, "test.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-001")
```

</details>

<details>
<summary>Advanced: fires on while loop for XOR rule (L-SIMD-003)</summary>

#### fires on while loop for XOR rule (L-SIMD-003)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn xor_buf(a: [u8], b: [u8], n: i64):\n    var i = 0\n    while i < n:\n        out[i] = a[i] ^ b[i]\n        i = i + 1\n"
val warnings = lint_simd_xor_loop(source, "cipher.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-003")
```

</details>


</details>

<details>
<summary>Advanced: fires on while loop for memcpy rule (L-SIMD-006)</summary>

#### fires on while loop for memcpy rule (L-SIMD-006)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn copy_buf(src: [u8], n: i64):\n    var i = 0\n    while i < n:\n        out[i] = src[i]\n        i = i + 1\n"
val warnings = lint_simd_memcpy_loop(source, "copy.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-006")
```

</details>


</details>

<details>
<summary>Advanced: fires on while loop for reduce_sum rule (L-SIMD-002)</summary>

#### fires on while loop for reduce_sum rule (L-SIMD-002)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: last_accum_var tracks the most recent `var X = 0` declaration.
# The source must have exactly one `var X = 0` before the while loop to avoid
# the heuristic being clobbered by a second declaration (e.g. `var i = 0`).
# Use a source with `var s = 0` immediately before the while loop.
val source = "fn sum_arr(a: [i32], n: i64) -> i64:\n    var s = 0\n    while s < n:\n        s = s + a[s]\n    s\n"
val warnings = lint_simd_reduce_sum(source, "test.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-002")
```

</details>


</details>

<details>
<summary>Advanced: fires on while loop for const shift rule (L-SIMD-005)</summary>

#### fires on while loop for const shift rule (L-SIMD-005)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn shift_arr(a: [i32], n: i64):\n    var i = 0\n    while i < n:\n        out[i] = a[i] >> 3\n        i = i + 1\n"
val warnings = lint_simd_const_shr_loop(source, "bits.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-005")
```

</details>


</details>

#### negative: while loops with unsafe patterns still suppressed

<details>
<summary>Advanced: does not fire on while loop with I/O inside body</summary>

#### does not fire on while loop with I/O inside body

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn process(a: [i32], b: [i32], n: i64):\n    var i = 0\n    while i < n:\n        out[i] = a[i] + b[i]\n        print out[i]\n        i = i + 1\n"
val warnings = lint_simd_elementwise_add(source, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: does not fire on while loop with FFI call inside body</summary>

#### does not fire on while loop with FFI call inside body

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn process(a: [u8], b: [u8], n: i64):\n    var i = 0\n    while i < n:\n        out[i] = a[i] ^ b[i]\n        rt_mem_barrier()\n        i = i + 1\n"
val warnings = lint_simd_xor_loop(source, "cipher.spl")
expect(warnings.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: does not fire on while loop already using FixedVec</summary>

#### does not fire on while loop already using FixedVec

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn process(a: [i32], b: [i32], n: i64):\n    var i = 0\n    while i < n:\n        val v = FixedVec<i32>(elements: a, lanes: 4)\n        out[i] = a[i] + b[i]\n        i = i + 1\n"
val warnings = lint_simd_elementwise_add(source, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>


</details>

### Bug2: L-SIMD-006 has_src — RHS array detection

#### positive: pure copy loops now detected

<details>
<summary>Advanced: fires on out[i] = src[i] (for loop)</summary>

#### fires on out[i] = src[i] (for loop)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn copy_buf(src: [u8], n: i64):\n    for i in 0..n:\n        out[i] = src[i]\n"
val warnings = lint_simd_memcpy_loop(source, "copy.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-006")
```

</details>


</details>

#### fires on new_ptr[i] = ptr[i] (allocator-style copy)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn copy_region(ptr: [u8], copy_size: i64):\n    for i in 0..copy_size:\n        new_ptr[i] = ptr[i]\n"
val warnings = lint_simd_memcpy_loop(source, "allocator.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-006")
```

</details>

<details>
<summary>Advanced: fires on dst[i] = src[i] (while loop)</summary>

#### fires on dst[i] = src[i] (while loop)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn copy_buf(src: [u8], n: i64):\n    var i = 0\n    while i < n:\n        dst[i] = src[i]\n        i = i + 1\n"
val warnings = lint_simd_memcpy_loop(source, "copy.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-006")
```

</details>


</details>

#### negative: non-copy patterns do not fire

#### does not fire when RHS has arithmetic: out[i] = src[i] + 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn transform(src: [u8], n: i64):\n    for i in 0..n:\n        out[i] = src[i] + 1\n"
val warnings = lint_simd_memcpy_loop(source, "copy.spl")
expect(warnings.len()).to_equal(0)
```

</details>

#### does not fire when body is out[i] = constant (no RHS array index)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn fill(n: i64):\n    for i in 0..n:\n        out[i] = 0\n"
val warnings = lint_simd_memcpy_loop(source, "fill.spl")
expect(warnings.len()).to_equal(0)
```

</details>

#### does not fire when RHS index is different variable: out[i] = src[j]

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn scatter(src: [u8], n: i64):\n    for i in 0..n:\n        out[i] = src[j]\n"
val warnings = lint_simd_memcpy_loop(source, "scatter.spl")
expect(warnings.len()).to_equal(0)
```

</details>

### Bug3: _loop_body_is_safe — allowlist max/min/abs/clamp

#### positive: allowlisted functions enable detection

#### fires L-SIMD-009 on out[i] = max(a[i], 0) (was blocked by safe check)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn relu(a: [f32], n: i64):\n    for i in 0..n:\n        out[i] = max(a[i], 0)\n"
val warnings = lint_simd_relu(source, "ml.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-009")
```

</details>

#### fires L-SIMD-004 on out[i] = max(a[i], b[i]) (element-wise max)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn elemmax(a: [f32], b: [f32], n: i64):\n    for i in 0..n:\n        out[i] = max(a[i], b[i])\n"
val warnings = lint_simd_elementwise_max(source, "math.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-004")
```

</details>

<details>
<summary>Advanced: fires L-SIMD-009 on while loop with max(a[i], 0) body</summary>

#### fires L-SIMD-009 on while loop with max(a[i], 0) body

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn relu(a: [f32], n: i64):\n    var i = 0\n    while i < n:\n        out[i] = max(a[i], 0)\n        i = i + 1\n"
val warnings = lint_simd_relu(source, "ml.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("L-SIMD-009")
```

</details>


</details>

#### negative: non-allowlisted functions still block detection

#### does not fire when body contains sqrt( (not in allowlist)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn process(a: [f32], n: i64):\n    for i in 0..n:\n        out[i] = sqrt(a[i])\n"
val warnings = lint_simd_elementwise_add(source, "math.spl")
expect(warnings.len()).to_equal(0)
```

</details>

#### does not fire on L-SIMD-009 when body contains sqrt( instead of max(

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn process(a: [f32], n: i64):\n    for i in 0..n:\n        out[i] = sqrt(a[i])\n"
val warnings = lint_simd_relu(source, "math.spl")
expect(warnings.len()).to_equal(0)
```

</details>

#### does not fire when body contains arbitrary function: transform(a[i])

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn process(a: [f32], n: i64):\n    for i in 0..n:\n        out[i] = transform(a[i])\n"
val warnings = lint_simd_elementwise_max(source, "math.spl")
expect(warnings.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 70 |
| Active scenarios | 70 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
