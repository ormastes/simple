# Primitive API Lint Spec — Text Scanner Exemptions

> Tests the text-scanner lint (`check_primitive_api`) after Team W adds: SAME bare primitive is not flagged.

<!-- sdn-diagram:id=primitive_api_lint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=primitive_api_lint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

primitive_api_lint_spec -> std
primitive_api_lint_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=primitive_api_lint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Primitive API Lint Spec — Text Scanner Exemptions

Tests the text-scanner lint (`check_primitive_api`) after Team W adds: SAME bare primitive is not flagged.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | fix-primitive-api-suppressions |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/quality/code_quality/primitive_api_lint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the text-scanner lint (`check_primitive_api`) after Team W adds:
- D-1: pure-math exemption — `pub fn` where every param and return type is the
  SAME bare primitive is not flagged.
- D-2: extern fn exemption — lines starting with `extern fn` are never flagged.
- AC-7: `primitive_api` level is `deny` in `build_default_levels()` after Phase 2.

These specs WILL FAIL until Team W lands the exemptions and Phase 2 promotes the
level to `deny`. The existing integration spec at
`test/integration/app/primitive_api_lint_spec.spl` covers the base case;
this file covers the NEW exemption cases only.

## Scenarios

### primitive_api lint — D-1 pure-math exemption

#### AC-D1: should NOT flag pub fn with all-same-primitive args and return (i64)

1. "pub fn add
   - Expected: count_primitive_api_fixes(source) equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange: pure-math function — same type everywhere
val source =
    "pub fn add(a: i64, b: i64) -> i64:\n" +
    "    return a + b\n"
# Act + Assert: after Team W exemption, count must be 0
expect(count_primitive_api_fixes(source)).to_equal(0)
```

</details>

#### AC-D1: should NOT flag pub fn with all-same-primitive args and return (f64)

1. "pub fn lerp

2. "    return a +
   - Expected: count_primitive_api_fixes(source) equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "pub fn lerp(a: f64, b: f64, t: f64) -> f64:\n" +
    "    return a + (b - a) * t\n"
expect(count_primitive_api_fixes(source)).to_equal(0)
```

</details>

#### AC-D1: should NOT flag single-arg single-return same-primitive fn

1. "pub fn negate
   - Expected: count_primitive_api_fixes(source) equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "pub fn negate(x: i64) -> i64:\n" +
    "    return 0 - x\n"
expect(count_primitive_api_fixes(source)).to_equal(0)
```

</details>

#### AC-D1: should STILL flag pub fn with mixed primitive types (i64 param, i32 return)

1. "pub fn truncate


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Mixed types are NOT exempt — this must still fire
val source =
    "pub fn truncate(value: i64) -> i32:\n" +
    "    return value as i32\n"
expect(count_primitive_api_fixes(source)).to_be_greater_than(0)
```

</details>

#### AC-D1: should STILL flag pub fn with only a primitive return type (no params)

1. "pub fn get count


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "pub fn get_count() -> i64:\n" +
    "    return 0\n"
expect(count_primitive_api_fixes(source)).to_be_greater_than(0)
```

</details>

### primitive_api lint — D-2 extern fn exemption

#### AC-D2: should NOT flag extern fn with primitive args

1. "extern fn rt alloc
   - Expected: count_primitive_api_fixes(source) equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "extern fn rt_alloc(size: i64) -> i64\n"
expect(count_primitive_api_fixes(source)).to_equal(0)
```

</details>

#### AC-D2: should NOT flag extern fn with mixed primitive types

1. "extern fn rt read
   - Expected: count_primitive_api_fixes(source) equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "extern fn rt_read(fd: i32, buf: i64, len: i64) -> i32\n"
expect(count_primitive_api_fixes(source)).to_equal(0)
```

</details>

#### AC-D2: should STILL flag a regular pub fn that mirrors an extern signature

1. "pub fn wrap alloc

2. "    return rt alloc


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Same shape as extern, but declared pub fn — must still fire
val source =
    "pub fn wrap_alloc(size: i64) -> i32:\n" +
    "    return rt_alloc(size)\n"
expect(count_primitive_api_fixes(source)).to_be_greater_than(0)
```

</details>

### primitive_api lint — AC-7 deny level

#### AC-7: build_default_levels returns deny for primitive_api

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/90.tools/lint/_LintMain/config_and_model.spl")
expect(source.contains("levels[\"primitive_api\"] = \"deny\"")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
