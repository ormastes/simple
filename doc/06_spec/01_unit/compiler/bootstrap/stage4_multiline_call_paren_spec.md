# Stage4 Multiline Call Paren Specification

> Tests covering Stage 4 multiline call closing parens.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stage4 Multiline Call Paren Specification

## Scenarios

### Stage 4 multiline call closing parens

#### keeps every adapter call closing paren with its final lambda

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps every adapter call closing paren with its final lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps every adapter call closing paren with its final lambda")
val source = read_file("src/std/nogc_sync_mut/test_runner/test_executor_composite_jit_generic.spl")
expect(source).to_not_contain("\\: adapter.disconnect()\n    )")
expect(source).to_contain("\\: adapter.disconnect())")
```

</details>

#### keeps the adjacent multiline declaration closing paren with its final parameter

- keeps the adjacent multiline declaration closing paren with its final parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the adjacent multiline declaration closing paren with its final parameter")
val source = read_file("src/std/nogc_sync_mut/test_runner/test_executor_composite_jit_generic.spl")
expect(source).to_contain("disconnect_fn: fn()) -> TestFileResult:")
expect(source).to_not_contain("disconnect_fn: fn()\n) -> TestFileResult:")
```

</details>

#### keeps the QEMU replay-controller call closing paren with its final lambda

- keeps the QEMU replay-controller call closing paren with its final lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the QEMU replay-controller call closing paren with its final lambda")
val source = read_file("src/std/nogc_sync_mut/debug/remote/exec/adapter_qemu_rv32.spl")
expect(source).to_contain("\\addr, bytes: self_ref.write_code(addr, bytes))")
expect(source).to_not_contain("\\addr, bytes: self_ref.write_code(addr, bytes)\n        )")
```

</details>

#### normalizes every owned replay-controller adapter sibling

- normalizes every owned replay-controller adapter sibling


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes every owned replay-controller adapter sibling")
for path in [
    "src/lib/nogc_async_mut/debug/remote/exec/adapter_arduino_r4.spl",
    "src/lib/nogc_async_mut/debug/remote/exec/adapter_ch32v307.spl",
    "src/lib/nogc_async_mut/debug/remote/exec/adapter_ghdl_rv32.spl",
    "src/lib/nogc_async_mut/debug/remote/exec/adapter_qemu_arm.spl",
    "src/lib/nogc_async_mut/debug/remote/exec/adapter_qemu_rv32.spl",
    "src/lib/nogc_async_mut/debug/remote/exec/adapter_stm32h7.spl",
    "src/lib/nogc_async_mut/debug/remote/exec/adapter_stm32wb.spl",
    "src/lib/nogc_async_mut/debug/remote/exec/adapter_trace32.spl",
    "src/lib/nogc_sync_mut/debug/remote/exec/adapter_arduino_r4.spl",
    "src/lib/nogc_sync_mut/debug/remote/exec/adapter_ch32v307.spl",
    "src/lib/nogc_sync_mut/debug/remote/exec/adapter_ghdl_rv32.spl",
    "src/lib/nogc_sync_mut/debug/remote/exec/adapter_qemu_arm.spl",
    "src/lib/nogc_sync_mut/debug/remote/exec/adapter_stm32h7.spl",
    "src/lib/nogc_sync_mut/debug/remote/exec/adapter_stm32wb.spl",
    "src/lib/nogc_sync_mut/debug/remote/exec/adapter_trace32.spl",
    "src/lib/nogc_sync_mut/debug/remote/exec/adapter_uno_q.spl"
]:
    val source = read_file(path)
    expect(source).to_not_contain("write_code(addr, bytes)\n        )")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/stage4_multiline_call_paren_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Stage 4 multiline call closing parens.
- Stage 4 multiline call closing parens

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f1702f8bc14fe13957b001f2a8e9c0fcee0fc77b18c183dddaa2553a09f0a402`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f1702f8bc14fe13957b001f2a8e9c0fcee0fc77b18c183dddaa2553a09f0a402`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f1702f8bc14fe13957b001f2a8e9c0fcee0fc77b18c183dddaa2553a09f0a402`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/bootstrap/stage4_multiline_call_paren_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/stage4_multiline_call_paren_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/bootstrap/stage4_multiline_call_paren_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/stage4_multiline_call_paren_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap/stage4_multiline_call_paren_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every adapter call closing paren with its final lambda' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/stage4_multiline_call_paren_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the adjacent multiline declaration closing paren with its final parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/stage4_multiline_call_paren_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the QEMU replay-controller call closing paren with its final lambda' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
