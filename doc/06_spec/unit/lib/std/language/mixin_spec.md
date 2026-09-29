# Mixin Feature Specification

> mixin MixinName<T>:

<details>
<summary>Full Scenario Manual</summary>

# Mixin Feature Specification

mixin MixinName<T>:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/std/language/mixin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Features

- **Field composition**: Add fields from mixins to classes
- **Method composition**: Add methods from mixins to classes
- **Generic mixins**: Parameterize mixins with type variables
- **Multiple mixins**: Apply multiple mixins to a single class
- **Type safety**: Full type checking and inference for mixin usage

## Syntax

```simple
mixin MixinName<T>:
    field_name: Type

    fn method_name(param: T) -> ReturnType:
        # implementation

class ClassName:
    use MixinName<ConcreteType>
    # class body
```

## Examples

Basic mixin with timestamp fields:

```simple
mixin Timestamp:
    var created_at: i64
    var updated_at: i64

class User:
    use Timestamp
    var name: text
```

Generic mixin for logging:

```simple
mixin Logger<T>:
    var log_level: i32

    fn log(message: T):
        print(message)

class Service:
    use Logger<text>
```

Multiple mixins composition:

```simple
class Document:
    use Timestamp
    use Logger<text>
    var content: text
```

## Scenarios

### Mixin - Basic Declaration

### Mixin - Method Declaration

### Mixin - Generic Parameters

### Mixin - Class Application

### Mixin - Multiple Composition

### Mixin - Type Inference

### Mixin - Name Conflicts

### Mixin - Generic Substitution


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `825f79b1b44a8439d12761bb0929e218cbf1388bb855219b836515ab865ba5ac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `825f79b1b44a8439d12761bb0929e218cbf1388bb855219b836515ab865ba5ac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `825f79b1b44a8439d12761bb0929e218cbf1388bb855219b836515ab865ba5ac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/unit/lib/std/language/mixin_spec.spl
mirror: doc/06_spec/unit/lib/std/language/mixin_spec.md (current)
findings: 4 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=81; blocker cap makes effective=49
doc/06_spec/unit/lib/std/language/mixin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/std/language/mixin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/std/language/mixin_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/lib/std/language/mixin_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
<!-- sspec-maintain:scorecard:end -->
