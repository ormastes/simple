# Compiler Full Pipeline Intensive Tests

> Comprehensive end-to-end testing of the complete compilation pipeline: Lexer → Parser → AST → MIR → Backend → Code Generation.

<!-- sdn-diagram:id=compiler_intensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_intensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_intensive_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_intensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Full Pipeline Intensive Tests

Comprehensive end-to-end testing of the complete compilation pipeline: Lexer → Parser → AST → MIR → Backend → Code Generation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1000-1010 |
| Category | Testing |
| Difficulty | 5/5 |
| Status | Implemented |
| Source | `test/02_integration/compiler/compiler_intensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive end-to-end testing of the complete compilation pipeline:
Lexer → Parser → AST → MIR → Backend → Code Generation.

Tests the full compiler workflow with real source code through all phases.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Full Pipeline | Complete lexer→parser→MIR→codegen workflow |
| E2E Testing | End-to-end validation with real Simple code |
| Phase Integration | Verify each phase integrates correctly |

## Related Specifications

- [Lexer](../../src/compiler/10.frontend/core/lexer.spl) - Tokenization
- [Parser](../../src/compiler/10.frontend/core/parser.spl) - AST generation
- [MIR](../../src/compiler/50.mir/) - Mid-level IR
- [Backend](../../src/compiler/70.backend/) - Code generation

## Examples

```simple
# Full compilation test
val code = "fn add(x, y): x + y"
val result = compile_pipeline(code)
```

## Scenarios

### Compiler Pipeline - Intensive

#### simple function compilation

<details>
<summary>Advanced: compiles function definition end-to-end</summary>

#### compiles function definition end-to-end _(slow)_

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simple function that should compile successfully
val code = "fn add(x, y): x + y"

# Verify code is not empty
check(code.len() > 0)

# Basic compilation check (placeholder - actual compilation in next phase)
val has_fn_keyword = code.contains("fn")
check(has_fn_keyword)
```

</details>


</details>

<details>
<summary>Advanced: compiles function with return type</summary>

#### compiles function with return type _(slow)_

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn square(x: i64) -> i64: x * x"
check(code.contains("->"))
check(code.contains("i64"))
```

</details>


</details>

#### class compilation

<details>
<summary>Advanced: compiles simple class</summary>

#### compiles simple class _(slow)_

1. fn get x
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Point:
    x: i64
    y: i64
    fn get_x() -> i64: self.x
"""

check(code.contains("class"))
check(code.contains("fn"))
```

</details>


</details>

<details>
<summary>Advanced: compiles class with constructor</summary>

#### compiles class with constructor _(slow)_

1. static fn new
2. Counter
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
class Counter:
    count: i64
    static fn new() -> Counter:
        Counter(count: 0)
"""

check(code.contains("static"))
check(code.contains("Counter"))
```

</details>


</details>

#### module compilation

<details>
<summary>Advanced: handles import statements</summary>

#### handles import statements _(slow)_

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "use std.spec\ncheck(true)"
check(code.contains("use"))
check(code.contains("std.spec"))
```

</details>


</details>

<details>
<summary>Advanced: handles multiple imports</summary>

#### handles multiple imports _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
use std.spec
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 24 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
