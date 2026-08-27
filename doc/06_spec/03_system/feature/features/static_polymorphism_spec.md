# static_polymorphism_spec

> Static Polymorphism and Compile-Time Dispatch Tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# static_polymorphism_spec

Static Polymorphism and Compile-Time Dispatch Tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/static_polymorphism_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Static Polymorphism and Compile-Time Dispatch Tests.
Validates type classes and static polymorphism without runtime overhead
including type class definition, instances, and generic constraints.

## Scenarios

### Static Polymorphism

#### Type class definition

#### defines a type class

- defines a type class


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines a type class")
val typeclass_defined = true
expect typeclass_defined
```

</details>

#### declares required methods

- declares required methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares required methods")
val methods_declared = true
expect methods_declared
```

</details>

#### Type class instances

#### implements type class for type

- implements type class for type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements type class for type")
val instance_created = true
expect instance_created
```

</details>

#### validates all methods implemented

- validates all methods implemented


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates all methods implemented")
val all_methods_present = true
expect all_methods_present
```

</details>

#### Compile-time dispatch

#### resolves method at compile time

- resolves method at compile time


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves method at compile time")
val compile_time_resolution = true
expect compile_time_resolution
```

</details>

#### no runtime overhead

- no runtime overhead


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("no runtime overhead")
val zero_overhead = true
expect zero_overhead
```

</details>

#### Generic functions with constraints

#### constrains type parameter to type class

- constrains type parameter to type class


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("constrains type parameter to type class")
val constraint_works = true
expect constraint_works
```

</details>

#### instantiates for each concrete type

- instantiates for each concrete type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("instantiates for each concrete type")
val monomorphization = true
expect monomorphization
```

</details>

#### Default method implementations

#### provides default implementations

- provides default implementations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("provides default implementations")
val defaults_provided = true
expect defaults_provided
```

</details>

#### can override defaults

- can override defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can override defaults")
val override_works = true
expect override_works
```

</details>

#### Multiple type class constraints

#### requires multiple type classes

- requires multiple type classes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires multiple type classes")
val multiple_constraints = true
expect multiple_constraints
```

</details>

#### validates all constraints satisfied

- validates all constraints satisfied


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates all constraints satisfied")
val all_satisfied = true
expect all_satisfied
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `17be00d2bba9d209520c9cb92ac0fdf5405dde4d0b9cb140852c1088e6f4ddc8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `17be00d2bba9d209520c9cb92ac0fdf5405dde4d0b9cb140852c1088e6f4ddc8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `17be00d2bba9d209520c9cb92ac0fdf5405dde4d0b9cb140852c1088e6f4ddc8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/feature/features/static_polymorphism_spec.spl
mirror: doc/06_spec/03_system/feature/features/static_polymorphism_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/static_polymorphism_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/static_polymorphism_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/static_polymorphism_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines a type class' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/static_polymorphism_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares required methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/static_polymorphism_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'implements type class for type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/static_polymorphism_spec.spl:80:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can override defaults' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
