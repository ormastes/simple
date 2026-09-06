# primitive_receiver_trait_impl_dispatch_spec

> As a Simple developer writing `impl SomeTrait for i64` (or text, bool,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# primitive_receiver_trait_impl_dispatch_spec

As a Simple developer writing `impl SomeTrait for i64` (or text, bool,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/language/primitive_receiver_trait_impl_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

As a Simple developer writing `impl SomeTrait for i64` (or text, bool,
    f32, f64, or a struct), I want calling the trait method on a receiver of
    that exact type to invoke that impl's body, not some other impl's body
    and not silently nothing, regardless of which primitive type I chose.

## Scenarios

### impl Trait for <primitive> dispatches to the matching impl (interpret engine)

#### dispatches correctly on a struct receiver (control)

- dispatches correctly on a struct receiver (control)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches correctly on a struct receiver (control)")
assert_equal(ControlPoint(x: 1).marker_probe(), 5001)
```

</details>

#### dispatches correctly on a text receiver

- dispatches correctly on a text receiver


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches correctly on a text receiver")
assert_equal("x".marker_probe(), 1001)
```

</details>

#### dispatches correctly on an i64 receiver

- dispatches correctly on an i64 receiver


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches correctly on an i64 receiver")
assert_equal((7 as i64).marker_probe(), 1002)
```

</details>

#### dispatches correctly on a bool receiver

- dispatches correctly on a bool receiver


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches correctly on a bool receiver")
assert_equal(true.marker_probe(), 1004)
```

</details>

#### dispatches correctly on an f32 receiver

- dispatches correctly on an f32 receiver


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches correctly on an f32 receiver")
assert_equal((1.5 as f32).marker_probe(), 1006)
```

</details>

#### dispatches correctly on an f64 receiver

- dispatches correctly on an f64 receiver


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches correctly on an f64 receiver")
assert_equal((1.5 as f64).marker_probe(), 1007)
```

</details>

#### dispatches correctly on an i32 receiver [KNOWN BUG: collapses to the i64 impl, see bug doc]

- dispatches correctly on an i32 receiver [KNOWN BUG: collapses to the i64 impl, see bug doc]


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches correctly on an i32 receiver [KNOWN BUG: collapses to the i64 impl, see bug doc]")
# EXPECTED (RED until fixed): should reach the i32 impl and return 1003.
# MEASURED today: returns 1002 -- the i64 impl's value -- because
# primitive impls register under a bare, unqualified method name
# (trait_impl_lowering.spl:242-244), so i32/i64 collide on one key.
assert_equal((7 as i32).marker_probe(), 1003)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dd24bde5396cfbfef966ffad238815d75819634faebbe2ad7a562b617fc31144`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dd24bde5396cfbfef966ffad238815d75819634faebbe2ad7a562b617fc31144`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dd24bde5396cfbfef966ffad238815d75819634faebbe2ad7a562b617fc31144`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/language/primitive_receiver_trait_impl_dispatch_spec.spl
mirror: doc/06_spec/01_unit/language/primitive_receiver_trait_impl_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/language/primitive_receiver_trait_impl_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/language/primitive_receiver_trait_impl_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/language/primitive_receiver_trait_impl_dispatch_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches correctly on a struct receiver (control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/primitive_receiver_trait_impl_dispatch_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches correctly on a text receiver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/primitive_receiver_trait_impl_dispatch_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches correctly on an i64 receiver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
