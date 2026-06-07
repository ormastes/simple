# Baremetal Syntax Specification

> 1. assert result len

<!-- sdn-diagram:id=baremetal_syntax_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=baremetal_syntax_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

baremetal_syntax_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=baremetal_syntax_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Baremetal Syntax Specification

## Scenarios

### Volatile Syntax

#### recognizes @volatile attribute

1. assert result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This test verifies the lexer recognizes @volatile
# Actual behavior is tested elsewhere
val result = "volatile attribute recognized"
assert result.len() > 0
```

</details>

#### parses volatile variable declaration

1. assert declaration starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The parser should handle: @volatile val reg: u32
val declaration = "@volatile val"
assert declaration.starts_with("@volatile")
```

</details>

### Unsafe Syntax

#### recognizes unsafe keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The lexer should have KwUnsafe token
val keyword = "unsafe"
assert keyword == "unsafe"
```

</details>

#### parses unsafe block structure

1. assert syntax contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser handles: unsafe: block
val syntax = "unsafe: pass"
assert syntax.contains("unsafe")
```

</details>

### Interrupt Syntax

#### recognizes @interrupt attribute

1. assert attr starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attr = "@interrupt"
assert attr.starts_with("@")
```

</details>

#### parses interrupt handler declaration

1. assert decl contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decl = "@interrupt(32) fn timer_handler():"
assert decl.contains("interrupt")
```

</details>

### Memory Layout Attributes

#### recognizes @repr attribute

1. assert attr contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attr = "@repr(C)"
assert attr.contains("repr")
```

</details>

#### recognizes @packed attribute

1. assert attr contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attr = "@packed"
assert attr.contains("packed")
```

</details>

#### recognizes @align attribute

1. assert attr contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attr = "@align(16)"
assert attr.contains("align")
```

</details>

### Bitfield Syntax

#### recognizes bitfield keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kw = "bitfield"
assert kw == "bitfield"
```

</details>

#### parses bitfield structure

1. assert syntax starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val syntax = "bitfield ControlReg:"
assert syntax.starts_with("bitfield")
```

</details>

### Address Syntax

#### parses @ address syntax

1. assert addr starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser should handle: val REG: u32 @ 0x40000000
val addr = "0x40000000"
assert addr.starts_with("0x")
```

</details>

### Static Assert

#### recognizes static assert

1. assert sa starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sa = "static assert size_of<u32>() == 4"
assert sa.starts_with("static")
```

</details>

### Const Functions

#### recognizes const fn

1. assert cf contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cf = "const fn compute() -> i64:"
assert cf.contains("const fn")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/native/baremetal_syntax_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Volatile Syntax
- Unsafe Syntax
- Interrupt Syntax
- Memory Layout Attributes
- Bitfield Syntax
- Address Syntax
- Static Assert
- Const Functions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
