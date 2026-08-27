# Static and Const Declarations Specification

> Static and const declarations provide compile-time and runtime constants with different scoping and initialization rules: 1. `static val` - Module-level immutable constants with static lifetime 2. `static var` - Module-level mutable state (requires careful use) 3. `const` - Compile-time constants with inline optimization 4. `static fn` - Static methods accessible via type/module name

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
| Updated | 2026-08-26 |
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
use std.spec.step

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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses simple static value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses simple static value")
val source = "static val PI = 3.14159"
expect(source.len()).to_be_greater_than(0)
```

</details>

#### parses static value with type annotation

- parses static value with type annotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses static value with type annotation")
val source = "static val MAX_SIZE: i64 = 1000"
expect(source.len()).to_be_greater_than(0)
```

</details>

#### parses static value with complex expression

- parses static value with complex expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses static value with complex expression")
val source = "static val GREETING = \"Hello, \" + \"World\""
expect(source.len()).to_be_greater_than(0)
```

</details>

#### parses multiple static values

- parses multiple static values


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses multiple static values")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `761688f2501959ea5dd46a6d169154dcd6ad6d2d96707450d72b6b9a370035e0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `761688f2501959ea5dd46a6d169154dcd6ad6d2d96707450d72b6b9a370035e0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `761688f2501959ea5dd46a6d169154dcd6ad6d2d96707450d72b6b9a370035e0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/static_const_declarations_spec.spl
mirror: doc/06_spec/03_system/feature/usage/static_const_declarations_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/static_const_declarations_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/static_const_declarations_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/static_const_declarations_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses simple static value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/static_const_declarations_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses static value with type annotation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/static_const_declarations_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses static value with complex expression' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
