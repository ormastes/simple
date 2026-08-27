# Parser Error Recovery Specification

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Error Recovery Specification

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-ERR-001 to #PARSER-ERR-016 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/usage/parser_error_recovery_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Common Mistakes Detected

- Python: `def`, `None`, `True`, `False`
- Rust: `let mut`, `.<T>` turbofish, `!` macros
- TypeScript: `const`, `function`, `let`, `=>`
- Java: `public class`
- C: Type-first declarations (`int x`)

## API

```simple
use std.spec.step

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

- detects Python def


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects Python def")
# When someone writes 'def' instead of 'fn', parser should suggest 'fn'
expect true
```

</details>

#### suggests fn instead of def

- suggests fn instead of def


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("suggests fn instead of def")
# CommonMistake.PythonDef.message() would say: use 'fn' not 'def'
expect true
```

</details>

#### None keyword

#### does not flag ambiguous None without type information

- does not flag ambiguous None without type information


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not flag ambiguous None without type information")
# None is a valid Simple enum/unit variant, especially Option.None.
# Token-level recovery intentionally avoids warning on it.
expect true
```

</details>

#### does not flag None after = (valid Option)

- does not flag None after = (valid Option)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not flag None after = (valid Option)")
# None after '=' could be Option.None — this is valid Simple syntax
expect true
```

</details>

#### leaves nil guidance to typed diagnostics

- leaves nil guidance to typed diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("leaves nil guidance to typed diagnostics")
# The parser recovery pass cannot distinguish Python None from
# valid Simple variants; typed diagnostics may still suggest nil
# when a nil literal is actually required.
expect true
```

</details>

#### True/False keywords

#### detects Python True

- detects Python True


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects Python True")
# Parser should suggest lowercase 'true'
expect true
```

</details>

#### detects Python False

- detects Python False


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects Python False")
# Parser should suggest lowercase 'false'
expect true
```

</details>

#### self field access

#### accepts explicit self field access

- accepts explicit self field access
   - Expected: recovery does not contain `PythonSelf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts explicit self field access")
val recovery = read_file("src/compiler/10.frontend/parser/recovery.spl")
expect(recovery.contains("PythonSelf")).to_equal(false)
```

</details>

#### keeps explicit self for unambiguous mutation

- keeps explicit self for unambiguous mutation
   - Expected: guide contains `self._stop_tracking()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps explicit self for unambiguous mutation")
val guide = read_file("doc/07_guide/quick_reference/syntax_quick_reference.md")
expect(guide.contains("self._stop_tracking()")).to_equal(true)
```

</details>

### Rust Syntax Detection

#### let mut

#### detects Rust let mut

- detects Rust let mut


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects Rust let mut")
# Parser should suggest 'var' instead of 'let mut'
expect true
```

</details>

#### suggests var instead of let mut

- suggests var instead of let mut


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("suggests var instead of let mut")
# CommonMistake.RustLetMut.message() mentions 'var'
expect true
```

</details>

#### turbofish syntax

#### detects Rust turbofish .<T>

- detects Rust turbofish .<T>


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects Rust turbofish .<T>")
# Parser should detect .<T> and suggest Simple generics
expect true
```

</details>

#### macro syntax

#### detects Rust macro !

- detects Rust macro !


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects Rust macro !")
# Parser should detect ! after identifier
expect true
```

</details>

#### suggests @ instead of !

- suggests @ instead of !


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("suggests @ instead of !")
# CommonMistake.RustMacro.suggestion() mentions '@'
expect true
```

</details>

### TypeScript Syntax Detection

#### const keyword

#### detects TypeScript const

- detects TypeScript const


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects TypeScript const")
# Parser should suggest 'val' instead of 'const'
expect true
```

</details>

#### suggests val instead of const

- suggests val instead of const


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("suggests val instead of const")
# CommonMistake.TsConst.message() mentions 'val'
expect true
```

</details>

#### function keyword

#### detects TypeScript function

- detects TypeScript function


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects TypeScript function")
# Parser should suggest 'fn' instead of 'function'
expect true
```

</details>

#### suggests fn instead of function

- suggests fn instead of function


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("suggests fn instead of function")
# CommonMistake.TsFunction.message() mentions 'fn'
expect true
```

</details>

#### let keyword

#### detects TypeScript let

- detects TypeScript let


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects TypeScript let")
# Parser should suggest 'val' or 'var'
expect true
```

</details>

#### suggests val/var instead of let

- suggests val/var instead of let


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("suggests val/var instead of let")
# CommonMistake.TsLet.message() mentions 'val' or 'var'
expect true
```

</details>

#### arrow function

#### detects TypeScript arrow =>

- detects TypeScript arrow =>


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects TypeScript arrow =>")
# Parser should detect => and suggest lambda syntax
expect true
```

</details>

#### suggests lambda instead of arrow

- suggests lambda instead of arrow


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("suggests lambda instead of arrow")
# CommonMistake.TsArrowFunction.message() mentions 'lambda'
expect true
```

</details>

### Java Syntax Detection

#### public class

#### detects Java public class

- detects Java public class


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects Java public class")
# Parser should detect 'public class' and suggest Simple syntax
expect true
```

</details>

### C Syntax Detection

#### type-first declaration

#### detects C-style int x

- detects C-style int x


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects C-style int x")
# Parser should suggest 'val x: i64' instead of 'int x'
expect true
```

</details>

#### detects C-style float y

- detects C-style float y


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects C-style float y")
# Parser should suggest 'val y: f64' instead of 'float y'
expect true
```

</details>

#### suggests type-after syntax

- suggests type-after syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("suggests type-after syntax")
# CommonMistake.CTypeFirst.message() mentions 'Type comes after' or 'val'
expect true
```

</details>

#### suggests val in suggestion

- suggests val in suggestion


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("suggests val in suggestion")
# CommonMistake.CTypeFirst.suggestion() mentions 'val'
expect true
```

</details>

### Bracket Syntax Detection

#### generic brackets

#### detects wrong brackets for generics

- detects wrong brackets for generics


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects wrong brackets for generics")
# Using [] instead of <> for generics should be caught
expect true
```

</details>

#### suggests angle brackets

- suggests angle brackets


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("suggests angle brackets")
# CommonMistake.WrongBrackets.suggestion() mentions '<>'
expect true
```

</details>

### Common Mistake Messages

#### PythonDef message mentions fn

- PythonDef message mentions fn


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("PythonDef message mentions fn")
# CommonMistake.PythonDef.message() contains "fn"
expect true
```

</details>

#### None is not exposed as a parser common-mistake message

- None is not exposed as a parser common-mistake message


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("None is not exposed as a parser common-mistake message")
# None is valid Simple syntax; no parser common-mistake is exposed.
expect true
```

</details>

#### RustLetMut message mentions var

- RustLetMut message mentions var


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("RustLetMut message mentions var")
# CommonMistake.RustLetMut.message() contains "var"
expect true
```

</details>

#### TsConst message mentions val

- TsConst message mentions val


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("TsConst message mentions val")
# CommonMistake.TsConst.message() contains "val"
expect true
```

</details>

#### TsFunction message mentions fn

- TsFunction message mentions fn


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("TsFunction message mentions fn")
# CommonMistake.TsFunction.message() contains "fn"
expect true
```

</details>

### Common Mistake Suggestions

#### PythonDef suggests fn

- PythonDef suggests fn


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("PythonDef suggests fn")
# CommonMistake.PythonDef.suggestion() contains "fn"
expect true
```

</details>

#### None has no parser common-mistake suggestion

- None has no parser common-mistake suggestion


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("None has no parser common-mistake suggestion")
# None is valid Simple syntax; token-level recovery does not suggest nil.
expect true
```

</details>

#### RustLetMut suggests var

- RustLetMut suggests var


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("RustLetMut suggests var")
# CommonMistake.RustLetMut.suggestion() contains "var"
expect true
```

</details>

#### TsConst suggests val

- TsConst suggests val


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("TsConst suggests val")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `87efc078007212d9a56b97c8243e8edb2ff427308c38d14da6ec2f0d4fae2081`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `87efc078007212d9a56b97c8243e8edb2ff427308c38d14da6ec2f0d4fae2081`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `87efc078007212d9a56b97c8243e8edb2ff427308c38d14da6ec2f0d4fae2081`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/parser_error_recovery_spec.spl
mirror: doc/06_spec/03_system/feature/usage/parser_error_recovery_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/parser_error_recovery_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/parser_error_recovery_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/parser_error_recovery_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects Python def' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_error_recovery_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'suggests fn instead of def' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_error_recovery_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag ambiguous None without type information' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
