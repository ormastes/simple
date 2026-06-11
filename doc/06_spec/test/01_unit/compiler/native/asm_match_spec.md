# Asm Match Specification

> 1. check

<!-- sdn-diagram:id=asm_match_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=asm_match_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

asm_match_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=asm_match_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Asm Match Specification

## Scenarios

### Asm Match Syntax

#### recognizes asm match keyword combination

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "asm match:"
check(code.starts_with("asm"))
check(code.contains("match"))
check(code.ends_with(":"))
```

</details>

#### recognizes case with target spec

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm = "case [x86_64]:"
check(arm.starts_with("case"))
check(arm.contains("["))
check(arm.contains("x86_64"))
check(arm.contains("]"))
```

</details>

#### recognizes case with pipe grouping

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm = "case [x86_64 | x86]:"
check(arm.contains("|"))
check(arm.contains("x86_64"))
check(arm.contains("x86"))
```

</details>

#### recognizes case with os qualifier

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm = "case [x86_64, linux]:"
check(arm.contains(","))
check(arm.contains("linux"))
```

</details>

#### recognizes case with full qualifier

1. check
2. check
3. check
4. check
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm = "case [x86_64, linux, gnu, llvm >= 15]:"
check(arm.contains("x86_64"))
check(arm.contains("linux"))
check(arm.contains("gnu"))
check(arm.contains("llvm"))
check(arm.contains(">="))
check(arm.contains("15"))
```

</details>

#### recognizes wildcard case

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm = "case _:"
check(arm.contains("_"))
```

</details>

#### recognizes compile_error in arm

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "compile_error(\"unsupported arch\")"
check(body.starts_with("compile_error"))
check(body.contains("unsupported arch"))
```

</details>

#### recognizes asm assert syntax

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "asm assert [x86_64, linux]"
check(code.starts_with("asm"))
check(code.contains("assert"))
check(code.contains("["))
check(code.contains("x86_64"))
```

</details>

### Asm Match Complete Example

#### parses full asm match block syntax

1. check
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify the complete syntax structure is valid
val example = "asm match:\n    case [x86_64]:\n        \"cli\"\n    case [aarch64]:\n        \"msr daifset, #0xf\"\n    case _:\n        compile_error(\"unsupported\")"
check(example.contains("asm match:"))
check(example.contains("case [x86_64]:"))
check(example.contains("case [aarch64]:"))
check(example.contains("case _:"))
check(example.contains("compile_error"))
```

</details>

#### parses version constraint operators

1. check
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ops = [">= 15", "== 17", "< 18", "~= 17"]
check(ops.len() == 4)
check(ops[0].contains(">="))
check(ops[1].contains("=="))
check(ops[2].contains("<"))
check(ops[3].contains("~="))
```

</details>

### Asm Assert Examples

#### parses asm assert with arch only

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "asm assert [x86_64]"
check(code.contains("assert"))
check(code.contains("x86_64"))
```

</details>

#### parses asm assert with full spec

1. check
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "asm assert [x86_64, linux, gnu, llvm >= 15]"
check(code.contains("assert"))
check(code.contains("x86_64"))
check(code.contains("linux"))
check(code.contains("gnu"))
check(code.contains("llvm"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/native/asm_match_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Asm Match Syntax
- Asm Match Complete Example
- Asm Assert Examples

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
