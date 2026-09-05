# Aop Predicate Parser Specification

> <details>

<!-- sdn-diagram:id=aop_predicate_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aop_predicate_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aop_predicate_parser_spec -> std
aop_predicate_parser_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aop_predicate_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aop Predicate Parser Specification

## Scenarios

### AOP Predicate Parser

### validate_predicate

#### accepts wildcard predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_predicate("*")).to_equal("")
```

</details>

#### accepts execution selector

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_predicate("execution(* foo(..))")).to_equal("")
```

</details>

#### accepts within selector

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_predicate("within(services.*)")).to_equal("")
```

</details>

#### accepts attr selector

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_predicate("attr(logged)")).to_equal("")
```

</details>

#### accepts AND operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_predicate("execution(* foo(..)) & attr(logged)")).to_equal("")
```

</details>

#### accepts OR operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_predicate("execution(* a(..)) | execution(* b(..))")).to_equal("")
```

</details>

#### accepts NOT operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_predicate("!execution(* skip(..))")).to_equal("")
```

</details>

#### accepts grouped expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_predicate("(execution(*) | within(svc.*)) & attr(tx)")).to_equal("")
```

</details>

#### rejects empty predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_predicate("")).to_start_with("E1501")
```

</details>

#### rejects deferred selector get

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_predicate("get(field)")).to_start_with("E1507")
```

</details>

#### rejects deferred selector set

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_predicate("set(field)")).to_start_with("E1507")
```

</details>

#### rejects deferred selector init

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_predicate("init(Type)")).to_start_with("E1507")
```

</details>

#### rejects deferred selector effect

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_predicate("effect(io)")).to_start_with("E1507")
```

</details>

#### rejects unknown selector

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_predicate("foobar(x)")).to_start_with("E1507")
```

</details>

#### rejects unmatched parenthesis

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_predicate("execution(* foo(..")).to_start_with("E1501")
```

</details>

### validate_advice_form

#### accepts before

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_advice_form("before")).to_equal("")
```

</details>

#### accepts after_success

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_advice_form("after_success")).to_equal("")
```

</details>

#### accepts after_error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_advice_form("after_error")).to_equal("")
```

</details>

#### accepts around

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_advice_form("around")).to_equal("")
```

</details>

#### rejects invalid form

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validate_advice_form("invalid")).to_start_with("E1503")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/aop_predicate_parser_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AOP Predicate Parser
- validate_predicate
- validate_advice_form

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
