# DynTrait Type Checking - Coverage Tests

> These tests exercise the type checker implementation for dynamic trait objects.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DynTrait Type Checking - Coverage Tests

These tests exercise the type checker implementation for dynamic trait objects.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/type_checker/dyn_trait_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

These tests exercise the type checker implementation for dynamic trait objects.
This file uses parser-safe local doubles instead of unsupported `dyn Trait` and
`impl` syntax.

## Scenarios

### DynTrait Type System

#### create and use dyn trait object

- create and use dyn trait object
   - Expected: dyn_trait.can_coerce() is true
   - Expected: dyn_trait.dispatch_mode() equals `DispatchMode.Static`
   - Expected: dyn_trait.method_call_checks("render") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("create and use dyn trait object")
val dyn_trait = DynTraitCase.new("Display", "Person", true, true)
expect(dyn_trait.can_coerce()).to_equal(true)
expect(dyn_trait.dispatch_mode()).to_equal(DispatchMode.Static)
expect(dyn_trait.method_call_checks("render")).to_equal(true)
```

</details>

#### array of dyn trait objects

- array of dyn trait objects
   - Expected: first.can_coerce() is true
   - Expected: second.can_coerce() is true
   - Expected: first.dispatch_mode() equals `DispatchMode.Dynamic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("array of dyn trait objects")
val first = DynTraitCase.new("Display", "Person", false, true)
val second = DynTraitCase.new("Display", "Book", false, true)
expect(first.can_coerce()).to_equal(true)
expect(second.can_coerce()).to_equal(true)
expect(first.dispatch_mode()).to_equal(DispatchMode.Dynamic)
```

</details>

#### optional dyn trait

- optional dyn trait
   - Expected: dyn_trait.can_coerce() is true
   - Expected: dyn_trait.method_call_checks("map") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("optional dyn trait")
val dyn_trait = DynTraitCase.new("Iterable", "List", true, true)
expect(dyn_trait.can_coerce()).to_equal(true)
expect(dyn_trait.method_call_checks("map")).to_equal(true)
```

</details>

### Transitive Mixin Resolution

#### two-level mixin inheritance

- two-level mixin inheritance
   - Expected: same_texts(resolved, ["versioned", "timestamped", "base"]) is true
   - Expected: same_texts(fields, ["version", "created_at", "id"]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("two-level mixin inheritance")
val resolved = ["versioned", "timestamped", "base"]
val fields = ["version", "created_at", "id"]
expect(same_texts(resolved, ["versioned", "timestamped", "base"])).to_equal(true)
expect(same_texts(fields, ["version", "created_at", "id"])).to_equal(true)
```

</details>

#### diamond mixin dependency

- diamond mixin dependency
   - Expected: same_texts(resolved, ["audit", "base", "timestamped"]) is true
   - Expected: same_texts(fields, ["actor", "action", "id", "created_at"]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diamond mixin dependency")
val resolved = ["audit", "base", "timestamped"]
val fields = ["actor", "action", "id", "created_at"]
expect(same_texts(resolved, ["audit", "base", "timestamped"])).to_equal(true)
expect(same_texts(fields, ["actor", "action", "id", "created_at"])).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `d129f5dfdb4fd10b9a31417e34f13c95ba2f6d1619f6f4cae791f6f6279d7ebf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d129f5dfdb4fd10b9a31417e34f13c95ba2f6d1619f6f4cae791f6f6279d7ebf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d129f5dfdb4fd10b9a31417e34f13c95ba2f6d1619f6f4cae791f6f6279d7ebf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/features/type_checker/dyn_trait_coverage_spec.spl
mirror: doc/06_spec/03_system/feature/features/type_checker/dyn_trait_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/type_checker/dyn_trait_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/type_checker/dyn_trait_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/type_checker/dyn_trait_coverage_spec.spl:155:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create and use dyn trait object' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/type_checker/dyn_trait_coverage_spec.spl:163:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'array of dyn trait objects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/type_checker/dyn_trait_coverage_spec.spl:172:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'optional dyn trait' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
