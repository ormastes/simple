# Dynamic Trait Objects (dyn Trait)

> Feature: Type inference for dynamic trait dispatch

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dynamic Trait Objects (dyn Trait)

Feature: Type inference for dynamic trait dispatch

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/type_inference/dyn_trait_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Feature: Type inference for dynamic trait dispatch
Category: Type System
Status: Executable coverage via local doubles

## Scenarios

### Dynamic Trait Objects

#### same dyn trait types unify

- same dyn trait types unify


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("same dyn trait types unify")
val checker = TypeChecker.new()
check(checker.unify(Type.dyn_trait("Display"), Type.dyn_trait("Display")))
```

</details>

#### different dyn trait types do not unify

- different dyn trait types do not unify


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("different dyn trait types do not unify")
val checker = TypeChecker.new()
check(not checker.unify(Type.dyn_trait("Display"), Type.dyn_trait("Debug")))
```

</details>

#### concrete type coerces to dyn Trait

- concrete type coerces to dyn Trait


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("concrete type coerces to dyn Trait")
val checker = TypeChecker.new()
checker.register_trait_impl("Display")
check(checker.can_coerce_to_dyn_trait("Person", "Display"))
```

</details>

#### dyn Trait in array types

- dyn Trait in array types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dyn Trait in array types")
val checker = TypeChecker.new()
check(checker.unify(Type.array("dyn Display"), Type.array("dyn Display")))
```

</details>

#### dyn Trait in Optional types

- dyn Trait in Optional types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dyn Trait in Optional types")
val checker = TypeChecker.new()
check(checker.unify(Type.optional("dyn Display"), Type.optional("dyn Display")))
```

</details>

#### static dispatch with interface binding

- static dispatch with interface binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("static dispatch with interface binding")
val checker = TypeChecker.new()
checker.bind_interface("Display")
check(checker.dispatch_mode("Display") == DispatchMode.Static)
```

</details>

#### dynamic dispatch without interface binding

- dynamic dispatch without interface binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dynamic dispatch without interface binding")
val checker = TypeChecker.new()
check(checker.dispatch_mode("Display") == DispatchMode.Dynamic)
```

</details>

#### cannot assign dyn Trait to concrete type

- cannot assign dyn Trait to concrete type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cannot assign dyn Trait to concrete type")
val checker = TypeChecker.new()
check(not checker.unify(Type.dyn_trait("Display"), Type.concrete("Person")))
```

</details>

#### dyn Trait method calls type check

- dyn Trait method calls type check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dyn Trait method calls type check")
val checker = TypeChecker.new()
checker.bind_interface("Display")
checker.register_method("render")
check(checker.method_call_type_checks("Display", "render"))
```

</details>

#### dyn Trait with generic methods

- dyn Trait with generic methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dyn Trait with generic methods")
val checker = TypeChecker.new()
checker.bind_interface("Iterable")
checker.register_method("map")
check(checker.method_call_type_checks("Iterable", "map"))
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

- Canonical SPipe generation for source `b5a832a85832fcc85e4837ce883b360a54a9798c8d73521dccc8b418c016a253`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b5a832a85832fcc85e4837ce883b360a54a9798c8d73521dccc8b418c016a253`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b5a832a85832fcc85e4837ce883b360a54a9798c8d73521dccc8b418c016a253`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/features/type_inference/dyn_trait_spec.spl
mirror: doc/06_spec/03_system/feature/features/type_inference/dyn_trait_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/type_inference/dyn_trait_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/type_inference/dyn_trait_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/type_inference/dyn_trait_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'same dyn trait types unify' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/type_inference/dyn_trait_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'different dyn trait types do not unify' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/type_inference/dyn_trait_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'concrete type coerces to dyn Trait' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
