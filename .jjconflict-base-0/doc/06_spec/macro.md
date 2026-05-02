# Simple Language Macros - Test Specification

This file contains executable test cases for Simple's macro system. Macros in Simple are hygienic, pattern-based, compile-time transformations. The current tests use local doubles (MacroRule, MacroExpander classes) to verify macro rule registration, application, arity checks, and hygiene.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #110-130 |
| Status | SPECIFICATION (Partially Implemented) |
| Type | Extracted Examples (Category B) |
| Reference | macro.md |
| Source | `test/specs/macro_spec.spl` |
| Updated | 2026-04-24 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

**Keywords:** macros, metaprogramming, code-generation, hygiene
**Topics:** metaprogramming, syntax, compile-time
**Symbols:** MacroRule, MacroExpander, HygienicScope, Template

## Overview

This file contains executable test cases for Simple's macro system.
Macros in Simple are hygienic, pattern-based, compile-time transformations.
The current tests use local doubles (MacroRule, MacroExpander classes) to
verify macro rule registration, application, arity checks, and hygiene.

The original specification file remains as architectural reference documentation.

**Note:** For complete specification text, design rationale, and architecture,
see doc/06_spec/macro.md

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


Token-based string interpolation (done at compile time):

    macro format!(template, args...):

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `summary.txt` | Text artifact | `build/test-artifacts/specs/macro/summary.txt` |

## Scenarios

- tracks macro arity
- expands positional placeholders
- leaves unrelated text intact
