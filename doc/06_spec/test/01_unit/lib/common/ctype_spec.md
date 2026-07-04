# Ctype Specification

> <details>

<!-- sdn-diagram:id=ctype_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ctype_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ctype_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ctype_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ctype Specification

## Scenarios

### ctype

#### classifies digits correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit(48)).to_equal(true)
expect(is_digit(57)).to_equal(true)
expect(is_digit(47)).to_equal(false)
expect(is_digit(58)).to_equal(false)
expect(is_digit(65)).to_equal(false)
```

</details>

#### classifies upper case correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_upper(65)).to_equal(true)
expect(is_upper(90)).to_equal(true)
expect(is_upper(64)).to_equal(false)
expect(is_upper(91)).to_equal(false)
expect(is_upper(97)).to_equal(false)
```

</details>

#### classifies lower case correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_lower(97)).to_equal(true)
expect(is_lower(122)).to_equal(true)
expect(is_lower(96)).to_equal(false)
expect(is_lower(123)).to_equal(false)
expect(is_lower(65)).to_equal(false)
```

</details>

#### classifies alpha correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha(65)).to_equal(true)
expect(is_alpha(90)).to_equal(true)
expect(is_alpha(97)).to_equal(true)
expect(is_alpha(122)).to_equal(true)
expect(is_alpha(48)).to_equal(false)
expect(is_alpha(32)).to_equal(false)
```

</details>

#### classifies alnum correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum(65)).to_equal(true)
expect(is_alnum(97)).to_equal(true)
expect(is_alnum(48)).to_equal(true)
expect(is_alnum(57)).to_equal(true)
expect(is_alnum(32)).to_equal(false)
expect(is_alnum(33)).to_equal(false)
```

</details>

#### classifies hex digits correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_xdigit(48)).to_equal(true)
expect(is_xdigit(57)).to_equal(true)
expect(is_xdigit(65)).to_equal(true)
expect(is_xdigit(70)).to_equal(true)
expect(is_xdigit(97)).to_equal(true)
expect(is_xdigit(102)).to_equal(true)
expect(is_xdigit(71)).to_equal(false)
expect(is_xdigit(103)).to_equal(false)
expect(is_xdigit(32)).to_equal(false)
```

</details>

#### classifies whitespace correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_space(32)).to_equal(true)
expect(is_space(9)).to_equal(true)
expect(is_space(10)).to_equal(true)
expect(is_space(13)).to_equal(true)
expect(is_space(11)).to_equal(true)
expect(is_space(12)).to_equal(true)
expect(is_space(65)).to_equal(false)
expect(is_space(48)).to_equal(false)
```

</details>

#### converts to lower case

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_lower(65)).to_equal(97)
expect(to_lower(90)).to_equal(122)
expect(to_lower(97)).to_equal(97)
expect(to_lower(48)).to_equal(48)
```

</details>

#### converts to upper case

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_upper(97)).to_equal(65)
expect(to_upper(122)).to_equal(90)
expect(to_upper(65)).to_equal(65)
expect(to_upper(48)).to_equal(48)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ctype_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ctype

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
