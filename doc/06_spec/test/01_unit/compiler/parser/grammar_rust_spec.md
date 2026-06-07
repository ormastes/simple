# Grammar Rust Specification

> 1. check

<!-- sdn-diagram:id=grammar_rust_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=grammar_rust_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

grammar_rust_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=grammar_rust_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Grammar Rust Specification

## Scenarios

### RustGrammar

#### creates Rust grammar

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grammar = MockRustGrammar.new()
check(grammar != nil)
```

</details>

#### parses Rust functions

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grammar = MockRustGrammar.new()
check(grammar.parse_functions())
```

</details>

#### parses Rust structs

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grammar = MockRustGrammar.new()
check(grammar.parse_structs())
```

</details>

#### handles Rust lifetimes

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grammar = MockRustGrammar.new()
check(grammar.handle_lifetimes())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/grammar_rust_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RustGrammar

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
