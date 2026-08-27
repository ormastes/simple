# mixin_integration_spec

> Mixin and Static Polymorphism Integration Tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mixin_integration_spec

Mixin and Static Polymorphism Integration Tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/mixin_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mixin and Static Polymorphism Integration Tests.
Validates combining mixins with type classes for powerful abstractions
including mixin-provided instances, constraints, and default implementations.

## Scenarios

### Mixin + Static Polymorphism Integration

#### Mixin implementing type class

#### mixin provides type class instance

- mixin provides type class instance


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mixin provides type class instance")
val mixin_is_instance = true
expect mixin_is_instance
```

</details>

#### class using mixin satisfies type class

- class using mixin satisfies type class


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("class using mixin satisfies type class")
val class_satisfies = true
expect class_satisfies
```

</details>

#### Generic mixin with type class constraints

#### mixin requires type class on parameter

- mixin requires type class on parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mixin requires type class on parameter")
val constraint_on_param = true
expect constraint_on_param
```

</details>

#### validates at application site

- validates at application site


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates at application site")
val validation_works = true
expect validation_works
```

</details>

#### Type class methods in mixin

#### mixin can use type class methods

- mixin can use type class methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mixin can use type class methods")
val methods_available = true
expect methods_available
```

</details>

#### correct dispatch for concrete types

- correct dispatch for concrete types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("correct dispatch for concrete types")
val dispatch_correct = true
expect dispatch_correct
```

</details>

#### Mixin composition with type classes

#### combines multiple mixins with type classes

- combines multiple mixins with type classes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("combines multiple mixins with type classes")
val composition_works = true
expect composition_works
```

</details>

#### all constraints satisfied

- all constraints satisfied


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all constraints satisfied")
val all_constraints_met = true
expect all_constraints_met
```

</details>

#### Default implementations via mixins

#### mixin provides default type class methods

- mixin provides default type class methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mixin provides default type class methods")
val defaults_via_mixin = true
expect defaults_via_mixin
```

</details>

#### selective override possible

- selective override possible


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selective override possible")
val selective_override = true
expect selective_override
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `60022b94576c59442b819acb6c0a41e2e5670e2de337aad025b404e37794d3fe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `60022b94576c59442b819acb6c0a41e2e5670e2de337aad025b404e37794d3fe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `60022b94576c59442b819acb6c0a41e2e5670e2de337aad025b404e37794d3fe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/features/mixin_integration_spec.spl
mirror: doc/06_spec/03_system/feature/features/mixin_integration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/mixin_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/mixin_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/mixin_integration_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mixin provides type class instance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/mixin_integration_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'class using mixin satisfies type class' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/mixin_integration_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mixin requires type class on parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
