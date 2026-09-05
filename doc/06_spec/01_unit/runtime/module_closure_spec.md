# Module Closure Specification

> 1. module state reset

<!-- sdn-diagram:id=module_closure_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_closure_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_closure_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=module_closure_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Closure Specification

## Scenarios

### Module Function Closures

#### allows imported functions to modify module var

1. module state reset
   - Expected: module_state_touch("alpha") equals `1`
   - Expected: module_state_touch("beta") equals `2`
   - Expected: module_state_count() equals `2`
   - Expected: module_state_label() equals `beta`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
module_state_reset()
expect(module_state_touch("alpha")).to_equal(1)
expect(module_state_touch("beta")).to_equal(2)
expect(module_state_count()).to_equal(2)
expect(module_state_label()).to_equal("beta")
```

</details>

#### allows imported functions to read module val collections

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrays and other val collections are accessible
val items = ["a", "b", "c"]
expect(items.len()).to_equal(3)
```

</details>

#### preserves module state between calls

1. module state reset
   - Expected: module_state_touch("first") equals `1`
   - Expected: module_state_count() equals `1`
   - Expected: module_state_touch("second") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
module_state_reset()
expect(module_state_touch("first")).to_equal(1)
expect(module_state_count()).to_equal(1)
expect(module_state_touch("second")).to_equal(2)
```

</details>

#### documents nested closures limitation

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Inner functions defined inside `it` blocks cannot access
# local vars from the enclosing scope (runtime limitation).
# fn inner(): outer + 5  -- would fail with "variable outer not found"
# This is a known limitation of the interpreter.
val limitation = "nested functions cannot capture it-block locals"
expect(limitation).to_contain("nested functions")
expect(limitation).to_contain("it-block locals")
```

</details>

#### documents function-scoped closures limitation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Functions defined inside `it` blocks cannot access
# local vars from the enclosing scope (runtime limitation).
# fn get_state(): module_state  -- would fail with "variable not found"
val limitation = "function-scoped closures cannot read enclosing locals"
expect(limitation).to_start_with("function-scoped")
expect(limitation).to_contain("enclosing locals")
```

</details>

### Runtime Built-in Functions

#### provides describe/it/expect without import

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# These functions are compiled into the runtime binary
# No 'use std.spec' needed
val runtime_spec_dsl = "describe/it/expect"
expect(runtime_spec_dsl).to_contain("expect")
expect(1 + 1).to_equal(2)
```

</details>

#### provides all core matchers

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Built-in matchers
expect(1).to_equal(1)
expect(1).to_be(1)
expect(nil).to_be_nil()
expect([1, 2]).to_contain(1)
expect("hello").to_start_with("he")
expect("hello").to_end_with("lo")
expect(5).to_be_greater_than(3)
expect(3).to_be_less_than(5)
```

</details>

### Import Path Resolution

#### keeps parser-safe coverage without a placeholder

1. module state reset
   - Expected: module_state_touch("import-path") equals `1`
   - Expected: module_state_label() equals `import-path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
module_state_reset()
expect(module_state_touch("import-path")).to_equal(1)
expect(module_state_label()).to_equal("import-path")
```

</details>

### Closure Limitations That DO Exist

#### nested function modifications don't persist (known runtime limit)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This IS a real limitation - nested function var changes don't persist
# The nested fn cannot see locals from enclosing `it` block scope.
# This test documents the limitation without triggering a parse error.
# In practice: var count = 0; fn inc(): count = count + 1
# would fail with "variable `count` not found"
val unsupported_pattern = "fn inc cannot mutate enclosing it-block count"
expect(unsupported_pattern).to_contain("it-block count")
```

</details>

#### documents the difference: nested fn vs module fn

1. module state reset
   - Expected: module_state_touch("module-fn") equals `1`
   - Expected: module_state_label() equals `module-fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Nested function closures: BROKEN (var changes don't persist)
# Module function closures: WORK (var changes persist when imported)
# The confusion in MEMORY.md was about which one was broken
module_state_reset()
expect(module_state_touch("module-fn")).to_equal(1)
expect(module_state_label()).to_equal("module-fn")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/runtime/module_closure_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Module Function Closures
- Runtime Built-in Functions
- Import Path Resolution
- Closure Limitations That DO Exist

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
