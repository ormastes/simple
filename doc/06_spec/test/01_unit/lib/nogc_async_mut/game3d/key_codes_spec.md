# Key Codes Specification

> <details>

<!-- sdn-diagram:id=key_codes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=key_codes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

key_codes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=key_codes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 52 | 52 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Key Codes Specification

## Scenarios

### KeyCode

#### is_letter()

#### returns true for A

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.A.is_letter()).to_equal(true)
```

</details>

#### returns true for Z

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Z.is_letter()).to_equal(true)
```

</details>

#### returns true for M (middle letter)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.M.is_letter()).to_equal(true)
```

</details>

#### returns false for Space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Space.is_letter()).to_equal(false)
```

</details>

#### returns false for Num0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Num0.is_letter()).to_equal(false)
```

</details>

#### returns false for Num9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Num9.is_letter()).to_equal(false)
```

</details>

#### returns false for Escape

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Escape.is_letter()).to_equal(false)
```

</details>

#### is_digit()

#### returns true for Num0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Num0.is_digit()).to_equal(true)
```

</details>

#### returns true for Num5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Num5.is_digit()).to_equal(true)
```

</details>

#### returns true for Num9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Num9.is_digit()).to_equal(true)
```

</details>

#### returns false for A

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.A.is_digit()).to_equal(false)
```

</details>

#### returns false for Space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Space.is_digit()).to_equal(false)
```

</details>

#### returns false for F1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.F1.is_digit()).to_equal(false)
```

</details>

#### is_arrow()

#### returns true for Up

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Up.is_arrow()).to_equal(true)
```

</details>

#### returns true for Down

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Down.is_arrow()).to_equal(true)
```

</details>

#### returns true for Left

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Left.is_arrow()).to_equal(true)
```

</details>

#### returns true for Right

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Right.is_arrow()).to_equal(true)
```

</details>

#### returns false for A

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.A.is_arrow()).to_equal(false)
```

</details>

#### returns false for Space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Space.is_arrow()).to_equal(false)
```

</details>

#### returns false for Enter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Enter.is_arrow()).to_equal(false)
```

</details>

#### is_modifier()

#### returns true for LeftShift

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.LeftShift.is_modifier()).to_equal(true)
```

</details>

#### returns true for LeftCtrl

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.LeftCtrl.is_modifier()).to_equal(true)
```

</details>

#### returns true for LeftAlt

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.LeftAlt.is_modifier()).to_equal(true)
```

</details>

#### returns true for RightShift

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.RightShift.is_modifier()).to_equal(true)
```

</details>

#### returns true for RightCtrl

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.RightCtrl.is_modifier()).to_equal(true)
```

</details>

#### returns true for RightAlt

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.RightAlt.is_modifier()).to_equal(true)
```

</details>

#### returns false for A

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.A.is_modifier()).to_equal(false)
```

</details>

#### returns false for Space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Space.is_modifier()).to_equal(false)
```

</details>

#### returns false for Enter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Enter.is_modifier()).to_equal(false)
```

</details>

#### is_function_key()

#### returns true for F1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.F1.is_function_key()).to_equal(true)
```

</details>

#### returns true for F6 (middle key)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.F6.is_function_key()).to_equal(true)
```

</details>

#### returns true for F12

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.F12.is_function_key()).to_equal(true)
```

</details>

#### returns false for A

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.A.is_function_key()).to_equal(false)
```

</details>

#### returns false for Space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Space.is_function_key()).to_equal(false)
```

</details>

#### returns false for Enter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Enter.is_function_key()).to_equal(false)
```

</details>

#### to_i32()

#### returns 32 for Space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Space.to_i32()).to_equal(32)
```

</details>

#### returns 65 for A

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.A.to_i32()).to_equal(65)
```

</details>

#### returns 90 for Z

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Z.to_i32()).to_equal(90)
```

</details>

#### returns 48 for Num0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Num0.to_i32()).to_equal(48)
```

</details>

#### returns 57 for Num9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Num9.to_i32()).to_equal(57)
```

</details>

#### returns 256 for Escape

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Escape.to_i32()).to_equal(256)
```

</details>

#### returns 257 for Enter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Enter.to_i32()).to_equal(257)
```

</details>

#### returns 290 for F1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.F1.to_i32()).to_equal(290)
```

</details>

#### returns 301 for F12

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.F12.to_i32()).to_equal(301)
```

</details>

#### returns 340 for LeftShift

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.LeftShift.to_i32()).to_equal(340)
```

</details>

#### returns 346 for RightAlt

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.RightAlt.to_i32()).to_equal(346)
```

</details>

#### returns 0 for Unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Unknown.to_i32()).to_equal(0)
```

</details>

### MouseButton

#### to_i32()

#### returns 0 for Left

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MouseButton.Left.to_i32()).to_equal(0)
```

</details>

#### returns 1 for Right

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MouseButton.Right.to_i32()).to_equal(1)
```

</details>

#### returns 2 for Middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MouseButton.Middle.to_i32()).to_equal(2)
```

</details>

#### returns 3 for Button4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MouseButton.Button4.to_i32()).to_equal(3)
```

</details>

#### returns 4 for Button5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MouseButton.Button5.to_i32()).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/game3d/key_codes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- KeyCode
- MouseButton

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 52 |
| Active scenarios | 52 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
