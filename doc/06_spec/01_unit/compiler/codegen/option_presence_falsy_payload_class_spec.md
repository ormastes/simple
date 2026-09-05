# Option Presence Falsy Payload Class Specification

> Tests covering presence is independent of payload truthiness, on every engine.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Option Presence Falsy Payload Class Specification

## Scenarios

### presence is independent of payload truthiness, on every engine

#### covers every falsy payload under the cranelift JIT

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- covers every falsy payload under the cranelift JIT
- Run the run-path probe under SIMPLE_EXECUTION_MODE=jit
- Axis 1: integer zero — the payload that collides with the nil bit pattern today
- Axis 1: float zero — a different tag, same conceptual trap
- Axis 1: boolean false — falsy but unambiguously present
- Axis 1: the empty string, consumed through `??` so an absent-read would substitute the fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("covers every falsy payload under the cranelift JIT")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=jit")
val jit = run_probe_in_mode("jit")

step("Axis 1: integer zero — the payload that collides with the nil bit pattern today")
expect(jit).to_contain("PASS cond_zero_i64 = present")

step("Axis 1: float zero — a different tag, same conceptual trap")
expect(jit).to_contain("PASS cond_zero_f64 = present")

step("Axis 1: boolean false — falsy but unambiguously present")
expect(jit).to_contain("PASS cond_false_bool = present")

step("Axis 1: the empty string, consumed through `??` so an absent-read would substitute the fallback")
expect(jit).to_contain("PASS coalesce_empty_text = ")
```

</details>

#### covers every consumption form for the same present-zero subject

- covers every consumption form for the same present-zero subject
- Axis 2: `.?` in condition position — lowered to a bare rt_is_some call
- Axis 2: `.?` in value position — must yield the payload, not the nil sentinel
- Axis 2: `match` Some/None
- Axis 2: `??` — the most dangerous form, it silently swaps in the default


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("covers every consumption form for the same present-zero subject")
val jit = run_probe_in_mode("jit")

step("Axis 2: `.?` in condition position — lowered to a bare rt_is_some call")
expect(jit).to_contain("PASS cond_zero_i64 = present")

step("Axis 2: `.?` in value position — must yield the payload, not the nil sentinel")
expect(jit).to_contain("PASS value_dotq_zero_i64 = 0")

step("Axis 2: `match` Some/None")
expect(jit).to_contain("PASS match_zero_i64 = some")

step("Axis 2: `??` — the most dangerous form, it silently swaps in the default")
expect(jit).to_contain("PASS coalesce_zero_i64 = 0")
expect(jit).to_contain("PASS coalesce_zero_f64 = 0.0")

# Axis 2's fifth form, `.is_some()` / `.is_none()`, is intentionally
# absent: those two names are broken on the JIT lane by a separate
# method-DISPATCH defect (wrong for present and absent receivers
# alike), filed as
# doc/08_tracking/bug/jit_is_some_is_none_method_dispatch_gap_2026-08-17.md.
# See the note in the probe. Re-add when that is fixed.
```

</details>

#### keeps absence detectable, so the fix is not \

- keeps absence detectable, so the fix is not \
- Every cell above would also pass if presence were hardwired true; these rows are what forbid that
- And a failed parse stays distinguishable from a successful parse of "0" — the two-directions check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps absence detectable, so the fix is not \")
step("Every cell above would also pass if presence were hardwired true; these rows are what forbid that")
val jit = run_probe_in_mode("jit")

expect(jit).to_contain("PASS cond_absent_i64 = absent")
expect(jit).to_contain("PASS match_absent_i64 = none")
expect(jit).to_contain("PASS coalesce_absent_i64 = 99")

step("And a failed parse stays distinguishable from a successful parse of \"0\" — the two-directions check")
expect(jit).to_contain("PASS parse_fail_default = -1")
expect(jit).to_contain("PASS parse_ok_zero = 0")
```

</details>

#### holds on the interpreter too, so the engines cannot drift apart

- holds on the interpreter too, so the engines cannot drift apart
- The interpreter reaches presence through is_condition_present, a completely separate path from rt_is_none
- Both engines must satisfy the SAME absolute oracles — this is what catches a fix applied to only one lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("holds on the interpreter too, so the engines cannot drift apart")
step("The interpreter reaches presence through is_condition_present, a completely separate path from rt_is_none")
val interp = run_probe_in_mode("interpreter")

step("Both engines must satisfy the SAME absolute oracles — this is what catches a fix applied to only one lane")
expect(interp).to_contain("OPTION_PRESENCE_FALSY_PAYLOAD PROBE: ALL PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/option_presence_falsy_payload_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering presence is independent of payload truthiness, on every engine.
- presence is independent of payload truthiness, on every engine

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e7b5ff7c95673aec41852d496f4558e3744a8731134cb6117dfbea9baa3f9685`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e7b5ff7c95673aec41852d496f4558e3744a8731134cb6117dfbea9baa3f9685`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e7b5ff7c95673aec41852d496f4558e3744a8731134cb6117dfbea9baa3f9685`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/option_presence_falsy_payload_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/option_presence_falsy_payload_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/option_presence_falsy_payload_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/option_presence_falsy_payload_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/option_presence_falsy_payload_class_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covers every falsy payload under the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/option_presence_falsy_payload_class_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covers every consumption form for the same present-zero subject' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/option_presence_falsy_payload_class_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps absence detectable, so the fix is not \' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
