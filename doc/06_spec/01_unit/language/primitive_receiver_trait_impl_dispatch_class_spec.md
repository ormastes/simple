# primitive_receiver_trait_impl_dispatch_class_spec

> As a Simple developer writing `impl SomeTrait for i64` (or text, i32, u64,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# primitive_receiver_trait_impl_dispatch_class_spec

As a Simple developer writing `impl SomeTrait for i64` (or text, i32, u64,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/language/primitive_receiver_trait_impl_dispatch_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

As a Simple developer writing `impl SomeTrait for i64` (or text, i32, u64,
    bool, f32, f64), I want the trait method called on a receiver of that exact
    type to invoke THAT impl's body — the same body, on every execution engine
    the toolchain offers. A method that returns one answer under the
    interpreter, a different answer under the JIT, or no answer at all is a
    silently-wrong-results defect, not an engine detail.

## Scenarios

### impl Trait for <primitive Self> reaches the user impl on every engine

#### runs the probe at all under both engines

- runs the probe at all under both engines
- The probe must actually start under the interpreter — a scan that finds nothing may have scanned nothing
- And under the JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("runs the probe at all under both engines")
step("The probe must actually start under the interpreter — a scan that finds nothing may have scanned nothing")
val interp = run_probe_in_mode("interpreter")
expect(interp).to_contain("PRIMITIVE_TRAIT_IMPL_DISPATCH PROBE: begin")

step("And under the JIT")
val jit = run_probe_in_mode("jit")
expect(jit).to_contain("PRIMITIVE_TRAIT_IMPL_DISPATCH PROBE: begin")
```

</details>

#### dispatches to the matching impl for every primitive Self type under the interpreter

- dispatches to the matching impl for every primitive Self type under the interpreter
- Signed and text receivers
- Narrower signed widths must NOT collapse onto the i64 impl
- Unsigned widths must register an impl at all
- bool and both float widths
- The struct control proves the probe's trait machinery itself is sound
- And no arm may be missing: the probe's own verdict must be ALL PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("dispatches to the matching impl for every primitive Self type under the interpreter")
val interp = run_probe_in_mode("interpreter")

step("Signed and text receivers")
expect(interp).to_contain("PASS text_receiver")
expect(interp).to_contain("PASS i64_receiver")

step("Narrower signed widths must NOT collapse onto the i64 impl")
expect(interp).to_contain("PASS i32_receiver")

step("Unsigned widths must register an impl at all")
expect(interp).to_contain("PASS u64_receiver")

step("bool and both float widths")
expect(interp).to_contain("PASS bool_receiver")
expect(interp).to_contain("PASS f32_receiver")
expect(interp).to_contain("PASS f64_receiver")

step("The struct control proves the probe's trait machinery itself is sound")
expect(interp).to_contain("PASS struct_control")

step("And no arm may be missing: the probe's own verdict must be ALL PASS")
expect(interp).to_contain("PRIMITIVE_TRAIT_IMPL_DISPATCH PROBE: ALL PASS")
```

</details>

#### dispatches to the matching impl for every primitive Self type under the cranelift JIT

- dispatches to the matching impl for every primitive Self type under the cranelift JIT
- The JIT must reach the user impl, not a same-named runtime builtin and not a dispatch error
- A primitive receiver must never produce an unresolved-dispatch error


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("dispatches to the matching impl for every primitive Self type under the cranelift JIT")
val jit = run_probe_in_mode("jit")

step("The JIT must reach the user impl, not a same-named runtime builtin and not a dispatch error")
expect(jit).to_contain("PASS text_receiver")
expect(jit).to_contain("PASS i64_receiver")
expect(jit).to_contain("PASS i32_receiver")
expect(jit).to_contain("PASS u64_receiver")
expect(jit).to_contain("PASS bool_receiver")
expect(jit).to_contain("PASS f32_receiver")
expect(jit).to_contain("PASS f64_receiver")
expect(jit).to_contain("PASS struct_control")

step("A primitive receiver must never produce an unresolved-dispatch error")
expect(jit).to_contain("PRIMITIVE_TRAIT_IMPL_DISPATCH PROBE: ALL PASS")
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

- `REQ-SSPEC-LANGUAGE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0775eb950d319f8d7b814e1b459a505d78ef4a437ee31aa05fc8f1765a457961`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0775eb950d319f8d7b814e1b459a505d78ef4a437ee31aa05fc8f1765a457961`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0775eb950d319f8d7b814e1b459a505d78ef4a437ee31aa05fc8f1765a457961`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/language/primitive_receiver_trait_impl_dispatch_class_spec.spl
mirror: doc/06_spec/01_unit/language/primitive_receiver_trait_impl_dispatch_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/language/primitive_receiver_trait_impl_dispatch_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/language/primitive_receiver_trait_impl_dispatch_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/language/primitive_receiver_trait_impl_dispatch_class_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs the probe at all under both engines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/primitive_receiver_trait_impl_dispatch_class_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches to the matching impl for every primitive Self type under the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/primitive_receiver_trait_impl_dispatch_class_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches to the matching impl for every primitive Self type under the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
