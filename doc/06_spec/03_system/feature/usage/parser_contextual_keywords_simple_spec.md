# Contextual Keyword Disambiguation

> Simple treats `skip`, `static`, and `default` as contextual keywords rather than fully reserved words. This means each token can serve as either a keyword or an ordinary identifier depending on syntactic context -- specifically, whether it is followed by `(`. The spec validates all six disambiguation branches (keyword vs identifier for each of the three tokens), confirms that multiple contextual keywords can coexist as method names within a single class, and ensures that identifiers merely prefixed with a keyword name (e.g., `skip_all`) are never misinterpreted.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contextual Keyword Disambiguation

Simple treats `skip`, `static`, and `default` as contextual keywords rather than fully reserved words. This means each token can serve as either a keyword or an ordinary identifier depending on syntactic context -- specifically, whether it is followed by `(`. The spec validates all six disambiguation branches (keyword vs identifier for each of the three tokens), confirms that multiple contextual keywords can coexist as method names within a single class, and ensures that identifiers merely prefixed with a keyword name (e.g., `skip_all`) are never misinterpreted.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-012 |
| Category | Syntax |
| Status | Active |
| Source | `test/03_system/feature/usage/parser_contextual_keywords_simple_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Simple treats `skip`, `static`, and `default` as contextual keywords rather than
fully reserved words. This means each token can serve as either a keyword or an
ordinary identifier depending on syntactic context -- specifically, whether it is
followed by `(`. The spec validates all six disambiguation branches (keyword vs
identifier for each of the three tokens), confirms that multiple contextual
keywords can coexist as method names within a single class, and ensures that
identifiers merely prefixed with a keyword name (e.g., `skip_all`) are never
misinterpreted.

## Syntax

```simple
# skip as identifier (followed by '(')
use std.spec.step

fn skip(n):
return n * 2
val result = skip(5)

# skip as keyword (standalone statement)
skip

# static as keyword in method declaration
class Math:
static fn add(a, b):
return a + b
Math.add(3, 7)

# default as identifier on a class method
class Settings:
fn default():
return 200
settings.default()
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Contextual keyword | A token that acts as a keyword or identifier based on surrounding syntax |
| Lookahead disambiguation | The parser checks for a following `(` to decide identifier vs keyword |
| Branch coverage | All six branches (keyword/identifier x three tokens) are exercised |
| Coexistence | A single class can define methods named `skip`, `static`, and `default` |

## Scenarios

### skip as identifier

#### works as function name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- works as function name


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works as function name")
fn skip(n):
    return n * 2
val result = skip(5)
expect result == 10
```

</details>

#### works as method name

- works as method name


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works as method name")
class MyClass:
    fn skip(n):
        return n + 1

val obj = MyClass()
val result = obj.skip(10)
expect result == 11
```

</details>

### skip as keyword

#### works as standalone statement

- works as standalone statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works as standalone statement")
skip
expect true
```

</details>

#### works in function body

- works in function body


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works in function body")
fn test():
    skip
    return 42
expect test() == 42
```

</details>

### static as identifier

#### works as function name

- works as function name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works as function name")
fn static():
    return "static func"
expect static() == "static func"
```

</details>

#### works as method name

- works as method name


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works as method name")
class Config:
    fn static():
        return 100

val cfg = Config()
expect cfg.static() == 100
```

</details>

### static as keyword

#### works in static method declaration

- works in static method declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works in static method declaration")
class Math:
    static fn add(a, b):
        return a + b

expect Math.add(3, 7) == 10
```

</details>

### default as identifier

#### works as function name

- works as function name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works as function name")
fn default():
    return "default val"
expect default() == "default val"
```

</details>

#### works as method name

- works as method name


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works as method name")
class Settings:
    fn default():
        return 200

val settings = Settings()
expect settings.default() == 200
```

</details>

### default as keyword

#### parses in match context

- parses in match context


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses in match context")
val x = 5
val result = match x:
    case 1: "one"
    case _: "other"
expect result == "other"
```

</details>

### edge cases

#### allows all three keywords as method names in same class

- allows all three keywords as method names in same class


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows all three keywords as method names in same class")
class Multi:
    fn skip():
        return 1

    fn static():
        return 2

    fn default():
        return 3

val obj = Multi()
expect obj.skip() == 1
expect obj.static() == 2
expect obj.default() == 3
```

</details>

#### distinguishes keywords from underscored identifiers

- distinguishes keywords from underscored identifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("distinguishes keywords from underscored identifiers")
val skip_all = 10
val static_var = 20
val default_value = 30
expect skip_all == 10
expect static_var == 20
expect default_value == 30
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `22b836649eb7ac0809781f74f6d59ba0a21fe1f410f129fcee022c4a0c29e577`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `22b836649eb7ac0809781f74f6d59ba0a21fe1f410f129fcee022c4a0c29e577`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `22b836649eb7ac0809781f74f6d59ba0a21fe1f410f129fcee022c4a0c29e577`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/parser_contextual_keywords_simple_spec.spl
mirror: doc/06_spec/03_system/feature/usage/parser_contextual_keywords_simple_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/parser_contextual_keywords_simple_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/parser_contextual_keywords_simple_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/parser_contextual_keywords_simple_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works as function name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_contextual_keywords_simple_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works as method name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_contextual_keywords_simple_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works as standalone statement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
