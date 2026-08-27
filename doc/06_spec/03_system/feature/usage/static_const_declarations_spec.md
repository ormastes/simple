# Static and Const Declarations Specification

> Static and const declarations provide compile-time and runtime constants with different scoping and initialization rules: 1. `static val` - Module-level immutable constants with static lifetime 2. `static var` - Module-level mutable state (requires careful use) 3. `const` - Compile-time constants with inline optimization 4. `static fn` - Static methods accessible via type/module name

<!-- sdn-diagram:id=static_const_declarations_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=static_const_declarations_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

static_const_declarations_spec -> math
static_const_declarations_spec -> config
static_const_declarations_spec -> utils
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=static_const_declarations_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 53 | 53 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static and Const Declarations Specification

Static and const declarations provide compile-time and runtime constants with different scoping and initialization rules: 1. `static val` - Module-level immutable constants with static lifetime 2. `static var` - Module-level mutable state (requires careful use) 3. `const` - Compile-time constants with inline optimization 4. `static fn` - Static methods accessible via type/module name

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #STATIC-001 to #STATIC-015 |
| Category | Language \| Declarations |
| Difficulty | 2/5 |
| Status | Planned |
| Source | `test/03_system/feature/usage/static_const_declarations_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Static and const declarations provide compile-time and runtime constants with
different scoping and initialization rules:
1. `static val` - Module-level immutable constants with static lifetime
2. `static var` - Module-level mutable state (requires careful use)
3. `const` - Compile-time constants with inline optimization
4. `static fn` - Static methods accessible via type/module name

## Syntax

```simple
# Static value (module-level constant)
static val PI = 3.14159
static val MAX_SIZE = 1000

# Static mutable (rare, requires synchronization)
static var counter = 0

# Const (compile-time constant)
const VERSION = "1.0.0"
const DEBUG = false

# Static method
impl Math:
static fn abs(n: i64) -> i64:
if n < 0: -n else: n

# Static method usage
val result = Math.abs(-42)
```

## Key Concepts

| Concept | Scope | Initialization | Mutability | Use Case |
|---------|-------|-----------------|-----------|----------|
| static val | Module | Runtime | Immutable | Constants, caches |
| static var | Module | Runtime | Mutable | State, counters |
| const | Module | Compile-time | Immutable | Literals, flags |
| static fn | Type | N/A | N/A | Factory, utility |

## Behavior

- Static values are initialized once at module load
- Constants are inlined at compile time
- Static methods do not receive `self` parameter
- Static var requires thread-safe access in concurrent contexts
- Statics are lazily initialized (first access)

## Related Specifications

- [Module System](module_system_spec.spl) - Scoping rules
- [Functions](functions_spec.spl) - Method definitions

## Scenarios

### Static Value Declaration

#### parses simple static value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "static val PI = 3.14159"
expect(source.len()).to_be_greater_than(0)
```

</details>

#### parses static value with type annotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "static val MAX_SIZE: i64 = 1000"
expect(source.len()).to_be_greater_than(0)
```

</details>

#### parses static value with complex expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "static val GREETING = \"Hello, \" + \"World\""
expect(source.len()).to_be_greater_than(0)
```

</details>

#### parses multiple static values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = """
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 53 |
| Active scenarios | 53 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
