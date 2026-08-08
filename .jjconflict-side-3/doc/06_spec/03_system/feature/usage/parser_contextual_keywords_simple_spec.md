# Contextual Keyword Disambiguation

> Simple treats `skip`, `static`, and `default` as contextual keywords rather than fully reserved words. This means each token can serve as either a keyword or an ordinary identifier depending on syntactic context -- specifically, whether it is followed by `(`. The spec validates all six disambiguation branches (keyword vs identifier for each of the three tokens), confirms that multiple contextual keywords can coexist as method names within a single class, and ensures that identifiers merely prefixed with a keyword name (e.g., `skip_all`) are never misinterpreted.

<!-- sdn-diagram:id=parser_contextual_keywords_simple_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_contextual_keywords_simple_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_contextual_keywords_simple_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_contextual_keywords_simple_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

1. fn skip


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn skip(n):
    return n * 2
val result = skip(5)
expect result == 10
```

</details>

#### works as method name

1. fn skip


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
expect true
```

</details>

#### works in function body

1. fn test
2. expect test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test():
    skip
    return 42
expect test() == 42
```

</details>

### static as identifier

#### works as function name

1. fn static
2. expect static


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn static():
    return "static func"
expect static() == "static func"
```

</details>

#### works as method name

1. fn static
2. expect cfg static


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Config:
    fn static():
        return 100

val cfg = Config()
expect cfg.static() == 100
```

</details>

### static as keyword

#### works in static method declaration

1. static fn add
2. expect Math add


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Math:
    static fn add(a, b):
        return a + b

expect Math.add(3, 7) == 10
```

</details>

### default as identifier

#### works as function name

1. fn default
2. expect default


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn default():
    return "default val"
expect default() == "default val"
```

</details>

#### works as method name

1. fn default
2. expect settings default


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Settings:
    fn default():
        return 200

val settings = Settings()
expect settings.default() == 200
```

</details>

### default as keyword

#### parses in match context

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val result = match x:
    case 1: "one"
    case _: "other"
expect result == "other"
```

</details>

### edge cases

#### allows all three keywords as method names in same class

1. fn skip
2. fn static
3. fn default
4. expect obj skip
5. expect obj static
6. expect obj default


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
