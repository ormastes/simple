# Simple Language Macros - Test Specification

> This file contains executable test cases for Simple's macro system. Macros in Simple are hygienic, pattern-based, compile-time transformations. The current tests use local doubles (MacroRule, MacroExpander classes) to verify macro rule registration, application, arity checks, and hygiene.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tracks macro arity
   - Expected: rule.arity() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks macro arity")
val rule = MacroRule.new("assert_eq", ["left", "right"], "expect({{left}}).to_equal({{right}})")
expect(rule.arity()).to_equal(2)
```

</details>

#### expands positional placeholders

- expands positional placeholders
   - Expected: rule.expand(["42"]) equals `print(42)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expands positional placeholders")
val rule = MacroRule.new("log", ["value"], "print({{value}})")
expect(rule.expand(["42"])).to_equal("print(42)")
```

</details>

#### leaves unrelated text intact

- leaves unrelated text intact
   - Expected: rule.expand(["HELLO"]) equals `=== HELLO ===`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("leaves unrelated text intact")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `07f27d979b5e9d99a7cea057d36246cd5be95914e93dccbbc479339105c985fb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `07f27d979b5e9d99a7cea057d36246cd5be95914e93dccbbc479339105c985fb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `07f27d979b5e9d99a7cea057d36246cd5be95914e93dccbbc479339105c985fb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/language/macro_spec.spl
mirror: doc/06_spec/03_system/feature/language/macro_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/language/macro_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/language/macro_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/language/macro_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/language/macro_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks macro arity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/language/macro_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'expands positional placeholders' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/language/macro_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves unrelated text intact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
