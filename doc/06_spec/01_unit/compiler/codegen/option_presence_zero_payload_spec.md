# Option Presence Zero Payload Specification

> Tests covering a present optional holding zero is not absent.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Option Presence Zero Payload Specification

## Scenarios

### a present optional holding zero is not absent

#### reports a zero payload as present under the interpreter (control arm)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports a zero payload as present under the interpreter (control arm)
- Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter was correct throughout, so a red here means the probe is broken rather than the engine


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports a zero payload as present under the interpreter (control arm)")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The interpreter was correct throughout, so a red here means the probe is broken rather than the engine")
expect(interp).to_contain("OPTION_PRESENCE_FALSY_PAYLOAD PROBE: ALL PASS")
```

</details>

#### reports a zero payload as present under the cranelift JIT

- reports a zero payload as present under the cranelift JIT
- Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine the defect lived in
- `if o.?:` on a present i64? holding 0 took the else branch before the fix
- `match o:` on the same value selected `case None` before the fix
- `.?` in value position yielded the nil sentinel, so `?? 99` substituted 99 for a value that was there
- A FAILED parse must stay distinguishable from a successful parse of "0"
- And the whole probe passes, so no other row regressed


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports a zero payload as present under the cranelift JIT")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine the defect lived in")
val jit = run_probe_in_mode("jit")

step("`if o.?:` on a present i64? holding 0 took the else branch before the fix")
expect(jit).to_contain("PASS cond_zero_i64 = present")

step("`match o:` on the same value selected `case None` before the fix")
expect(jit).to_contain("PASS match_zero_i64 = some")

step("`.?` in value position yielded the nil sentinel, so `?? 99` substituted 99 for a value that was there")
expect(jit).to_contain("PASS value_dotq_zero_i64 = 0")

step("A FAILED parse must stay distinguishable from a successful parse of \"0\"")
expect(jit).to_contain("PASS parse_fail_default = -1")
expect(jit).to_contain("PASS parse_ok_zero = 0")

step("And the whole probe passes, so no other row regressed")
expect(jit).to_contain("OPTION_PRESENCE_FALSY_PAYLOAD PROBE: ALL PASS")
```

</details>

#### still reports a genuinely absent optional as absent

- still reports a genuinely absent optional as absent
- The fix must not degenerate into "everything is present" — absence still has to work


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still reports a genuinely absent optional as absent")
step("The fix must not degenerate into \"everything is present\" — absence still has to work")
val jit = run_probe_in_mode("jit")

expect(jit).to_contain("PASS cond_absent_i64 = absent")
expect(jit).to_contain("PASS match_absent_i64 = none")
expect(jit).to_contain("PASS coalesce_absent_i64 = 99")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/option_presence_zero_payload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering a present optional holding zero is not absent.
- a present optional holding zero is not absent

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `312c8d7e14f0b0ab656211d65a0799b939d476fbde3bb8a4595f3f3767b292a4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `312c8d7e14f0b0ab656211d65a0799b939d476fbde3bb8a4595f3f3767b292a4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `312c8d7e14f0b0ab656211d65a0799b939d476fbde3bb8a4595f3f3767b292a4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/option_presence_zero_payload_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/option_presence_zero_payload_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/option_presence_zero_payload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/option_presence_zero_payload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/option_presence_zero_payload_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a zero payload as present under the interpreter (control arm)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/option_presence_zero_payload_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a zero payload as present under the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/option_presence_zero_payload_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still reports a genuinely absent optional as absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
