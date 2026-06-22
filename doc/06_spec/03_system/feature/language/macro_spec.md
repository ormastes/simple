# Simple Language Macros - Test Specification

> This file contains executable test cases for Simple's macro system. Macros in Simple are hygienic, pattern-based, compile-time transformations. The current tests use local doubles (MacroRule, MacroExpander classes) to verify macro rule registration, application, arity checks, and hygiene.

<!-- sdn-diagram:id=macro_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Language Macros - Test Specification

This file contains executable test cases for Simple's macro system. Macros in Simple are hygienic, pattern-based, compile-time transformations. The current tests use local doubles (MacroRule, MacroExpander classes) to verify macro rule registration, application, arity checks, and hygiene.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #110-130 |
| Category | Other |
| Status | SPECIFICATION (Partially Implemented) |
| Type | Extracted Examples (Category B) |
| Reference | macro.md |
| Source | `test/03_system/feature/language/macro_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This file contains executable test cases for Simple's macro system.
Macros in Simple are hygienic, pattern-based, compile-time transformations.
The current tests use local doubles (MacroRule, MacroExpander classes) to
verify macro rule registration, application, arity checks, and hygiene.

The original specification file remains as architectural reference documentation.

**Note:** For complete specification text, design rationale, and architecture,
see doc/06_spec/feature/language/macro_spec.md

## Syntax

Define a macro with a pattern and template:

    macro swap!(a, b):
        val tmp = a
        a = b
        b = tmp

Invoke a macro at the call site:

    swap!(x, y)

Hygienic expansion (generated names don't leak into caller scope):

    macro make_counter!(name):
        var name_count: i64 = 0
        fn name_inc(): name_count = name_count + 1

## Examples

    val rule = MacroRule.new("swap", ["a", "b"], "val tmp = a; a = b; b = tmp")
    rule.name       # => "swap"
    rule.arity()    # => 2

    val expander = MacroExpander.new()
    expander.register(rule)
    expander.has_rule("swap")       # => true
    expander.expand("swap", ["x", "y"])  # => expanded text

    val scope = HygienicScope.new("swap_1")
    scope.fresh_name("tmp")  # => "tmp_swap_1"  (collision-free)

## Key Concepts

**Pattern-based macros** — macro rules match a source pattern and rewrite it
to a target template at compile time, before type checking.

**Hygiene** — generated identifiers are given unique internal names so they
cannot accidentally shadow or be shadowed by names in the caller's scope.

**Arity checking** — the compiler verifies that each macro call supplies
exactly the number of arguments the rule's pattern declares.

**Declarative macros** — the primary macro kind in Simple; match-and-replace
on syntax trees. No arbitrary code execution at compile time.

**Procedural macros** — planned extension: derive macros and attribute macros
that receive and emit syntax trees. Not yet fully implemented.

**Compile-time evaluation** — macros expand before runtime; side effects
inside a macro (allocation, I/O) are forbidden and rejected at parse time.

**Recursive macros** — a macro may call itself up to a configurable depth
limit (default: 64) to implement iteration patterns without native loops.

## Common Patterns

Assertion macro (compile-time message formatting):

    macro assert!(cond, msg):
        if not cond:
            panic("Assertion failed: {msg}")

Derive-style boilerplate generation:

    #[derive(Debug, Clone, Eq)]
    struct Point:
        x: i64
        y: i64

    # Expands to:
    # impl Debug for Point: fn debug() -> text: "Point({self.x}, {self.y})"
    # impl Clone for Point: fn clone() -> Point: Point(x: self.x, y: self.y)
    # impl Eq for Point:    fn eq(other: Point) -> bool: ...

Token-based string interpolation (done at compile time):

    macro format!(template, args...):
        # expands to a sequence of string concatenations
        # resolved entirely at compile time if args are literals

## Scenarios

### Macro

#### tracks macro arity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = MacroRule.new("assert_eq", ["left", "right"], "expect({{left}}).to_equal({{right}})")
expect(rule.arity()).to_equal(2)
```

</details>

#### expands positional placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = MacroRule.new("log", ["value"], "print({{value}})")
expect(rule.expand(["42"])).to_equal("print(42)")
```

</details>

#### leaves unrelated text intact

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = MacroRule.new("banner", ["title"], "=== {{title}} ===")
expect(rule.expand(["HELLO"])).to_equal("=== HELLO ===")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
