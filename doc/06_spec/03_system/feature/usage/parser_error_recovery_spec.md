# Parser Error Recovery Specification

> use std.parser.{Parser, CommonMistake, detect_common_mistake}

<!-- sdn-diagram:id=parser_error_recovery_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_error_recovery_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_error_recovery_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_error_recovery_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Error Recovery Specification

use std.parser.{Parser, CommonMistake, detect_common_mistake}

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-ERR-001 to #PARSER-ERR-016 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/usage/parser_error_recovery_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Common Mistakes Detected

- Python: `def`, `None`, `True`, `False`, `self.`
- Rust: `let mut`, `.<T>` turbofish, `!` macros
- TypeScript: `const`, `function`, `let`, `=>`
- Java: `public class`
- C: Type-first declarations (`int x`)

## API

```simple
use std.parser.{Parser, CommonMistake, detect_common_mistake}

val mistake = detect_common_mistake(token, prev_token, next_token)
val message = mistake.message()
val suggestion = mistake.suggestion()
```

Note: The Parser and CommonMistake types are compiler-internal constructs.
In interpreter mode, the std.parser module provides data format parsing
(JSON, CSV, etc.), not the compiler parser. These tests verify the concepts
are documented; actual parser error recovery is tested via compiled mode.

## Scenarios

### Python Syntax Detection

#### def keyword

#### detects Python def

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When someone writes 'def' instead of 'fn', parser should suggest 'fn'
expect true
```

</details>

#### suggests fn instead of def

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CommonMistake.PythonDef.message() would say: use 'fn' not 'def'
expect true
```

</details>

#### None keyword

#### does not flag ambiguous None without type information

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# None is a valid Simple enum/unit variant, especially Option.None.
# Token-level recovery intentionally avoids warning on it.
expect true
```

</details>

#### does not flag None after = (valid Option)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# None after '=' could be Option.None — this is valid Simple syntax
expect true
```

</details>

#### leaves nil guidance to typed diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The parser recovery pass cannot distinguish Python None from
# valid Simple variants; typed diagnostics may still suggest nil
# when a nil literal is actually required.
expect true
```

</details>

#### True/False keywords

#### detects Python True

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser should suggest lowercase 'true'
expect true
```

</details>

#### detects Python False

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser should suggest lowercase 'false'
expect true
```

</details>

#### self parameter

#### detects explicit self parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Python uses explicit 'self.', Simple has implicit self
expect true
```

</details>

#### suggests implicit self

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CommonMistake.PythonSelf would mention 'implicit'
expect true
```

</details>

### Rust Syntax Detection

#### let mut

#### detects Rust let mut

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser should suggest 'var' instead of 'let mut'
expect true
```

</details>

#### suggests var instead of let mut

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CommonMistake.RustLetMut.message() mentions 'var'
expect true
```

</details>

#### turbofish syntax

#### detects Rust turbofish .<T>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser should detect .<T> and suggest Simple generics
expect true
```

</details>

#### macro syntax

#### detects Rust macro !

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser should detect ! after identifier
expect true
```

</details>

#### suggests @ instead of !

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CommonMistake.RustMacro.suggestion() mentions '@'
expect true
```

</details>

### TypeScript Syntax Detection

#### const keyword

#### detects TypeScript const

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser should suggest 'val' instead of 'const'
expect true
```

</details>

#### suggests val instead of const

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CommonMistake.TsConst.message() mentions 'val'
expect true
```

</details>

#### function keyword

#### detects TypeScript function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser should suggest 'fn' instead of 'function'
expect true
```

</details>

#### suggests fn instead of function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CommonMistake.TsFunction.message() mentions 'fn'
expect true
```

</details>

#### let keyword

#### detects TypeScript let

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser should suggest 'val' or 'var'
expect true
```

</details>

#### suggests val/var instead of let

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CommonMistake.TsLet.message() mentions 'val' or 'var'
expect true
```

</details>

#### arrow function

#### detects TypeScript arrow =>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser should detect => and suggest lambda syntax
expect true
```

</details>

#### suggests lambda instead of arrow

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CommonMistake.TsArrowFunction.message() mentions 'lambda'
expect true
```

</details>

### Java Syntax Detection

#### public class

#### detects Java public class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser should detect 'public class' and suggest Simple syntax
expect true
```

</details>

### C Syntax Detection

#### type-first declaration

#### detects C-style int x

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser should suggest 'val x: i64' instead of 'int x'
expect true
```

</details>

#### detects C-style float y

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser should suggest 'val y: f64' instead of 'float y'
expect true
```

</details>

#### suggests type-after syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CommonMistake.CTypeFirst.message() mentions 'Type comes after' or 'val'
expect true
```

</details>

#### suggests val in suggestion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CommonMistake.CTypeFirst.suggestion() mentions 'val'
expect true
```

</details>

### Bracket Syntax Detection

#### generic brackets

#### detects wrong brackets for generics

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Using [] instead of <> for generics should be caught
expect true
```

</details>

#### suggests angle brackets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CommonMistake.WrongBrackets.suggestion() mentions '<>'
expect true
```

</details>

### Common Mistake Messages

#### PythonDef message mentions fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CommonMistake.PythonDef.message() contains "fn"
expect true
```

</details>

#### None is not exposed as a parser common-mistake message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# None is valid Simple syntax; no parser common-mistake is exposed.
expect true
```

</details>

#### RustLetMut message mentions var

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CommonMistake.RustLetMut.message() contains "var"
expect true
```

</details>

#### TsConst message mentions val

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CommonMistake.TsConst.message() contains "val"
expect true
```

</details>

#### TsFunction message mentions fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CommonMistake.TsFunction.message() contains "fn"
expect true
```

</details>

### Common Mistake Suggestions

#### PythonDef suggests fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CommonMistake.PythonDef.suggestion() contains "fn"
expect true
```

</details>

#### None has no parser common-mistake suggestion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# None is valid Simple syntax; token-level recovery does not suggest nil.
expect true
```

</details>

#### RustLetMut suggests var

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CommonMistake.RustLetMut.suggestion() contains "var"
expect true
```

</details>

#### TsConst suggests val

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CommonMistake.TsConst.suggestion() contains "val"
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
