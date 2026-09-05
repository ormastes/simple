# Optional Scalar Payload Roundtrip Specification

> Tests covering optional scalar payload round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Optional Scalar Payload Roundtrip Specification

## Scenarios

### optional scalar payload round-trip

#### renders an i64 optional bound from a literal as its payload

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders an i64 optional bound from a literal as its payload
- Bind a raw integer literal into an `i64?` slot
- Rendering must show the payload, not its bit pattern read as a float
   - Expected: x.to_string() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders an i64 optional bound from a literal as its payload")
step("Bind a raw integer literal into an `i64?` slot")
val x: i64? = 42

step("Rendering must show the payload, not its bit pattern read as a float")
expect(x.to_string()).to_equal("42")
```

</details>

#### unwraps a non-nil optional to its payload instead of nil

- unwraps a non-nil optional to its payload instead of nil
- `!` on a plainly non-nil optional must yield the payload
   - Expected: (x!).to_string() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unwraps a non-nil optional to its payload instead of nil")
step("`!` on a plainly non-nil optional must yield the payload")
val x: i64? = 42
expect((x!).to_string()).to_equal("42")
```

</details>

#### returns the payload from `??` and reaches the default only on nil

- returns the payload from `??` and reaches the default only on nil
- A non-nil optional coalesces to its own payload
   - Expected: (x ?? 99).to_string() equals `42`
- A nil optional is the only case that reaches the default
   - Expected: (n ?? 99).to_string() equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns the payload from `??` and reaches the default only on nil")
step("A non-nil optional coalesces to its own payload")
val x: i64? = 42
expect((x ?? 99).to_string()).to_equal("42")

step("A nil optional is the only case that reaches the default")
val n: i64? = nil
expect((n ?? 99).to_string()).to_equal("99")
```

</details>

#### carries the payload across a function return typed `i64?`

- carries the payload across a function return typed `i64?`
- Return a raw literal from a function declared `-> i64?`
- The returned value must render as 7, never as a tagged handle
   - Expected: g.to_string() equals `7`
   - Expected: (g!).to_string() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("carries the payload across a function return typed `i64?`")
step("Return a raw literal from a function declared `-> i64?`")
val g = give_int()

step("The returned value must render as 7, never as a tagged handle")
expect(g.to_string()).to_equal("7")
expect((g!).to_string()).to_equal("7")
```

</details>

#### agrees between the interpreter and the cranelift JIT on every optional read

- agrees between the interpreter and the cranelift JIT on every optional read
- Write the bug report's minimal repro to a temporary source file
- Run it under SIMPLE_EXECUTION_MODE=interpreter — the engine that was always correct
- Run the same file under SIMPLE_EXECUTION_MODE=jit — the engine that was wrong
- Both engines must produce the same absolute values
- Neither corruption signature may appear: the denormal, the raw tagged handle, or a nil unwrap
   - Expected: jit does not contain `0.0000000000000000000`
   - Expected: jit does not contain `<value:0x`
   - Expected: jit does not contain `bang_x=nil`
   - Expected: jit does not contain `bang_g=nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("agrees between the interpreter and the cranelift JIT on every optional read")
step("Write the bug report's minimal repro to a temporary source file")
step("Run it under SIMPLE_EXECUTION_MODE=interpreter — the engine that was always correct")
val interp = run_repro_in_mode("interpreter")

step("Run the same file under SIMPLE_EXECUTION_MODE=jit — the engine that was wrong")
val jit = run_repro_in_mode("jit")

step("Both engines must produce the same absolute values")
expect(interp).to_contain("x=42")
expect(interp).to_contain("bang_x=42")
expect(interp).to_contain("g=7")
expect(interp).to_contain("bang_g=7")
expect(interp).to_contain("coalesce=42")
expect(jit).to_contain("x=42")
expect(jit).to_contain("bang_x=42")
expect(jit).to_contain("g=7")
expect(jit).to_contain("bang_g=7")
expect(jit).to_contain("coalesce=42")

step("Neither corruption signature may appear: the denormal, the raw tagged handle, or a nil unwrap")
expect(jit.contains("0.0000000000000000000")).to_equal(false)
expect(jit.contains("<value:0x")).to_equal(false)
expect(jit.contains("bang_x=nil")).to_equal(false)
expect(jit.contains("bang_g=nil")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/optional_scalar_payload_roundtrip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering optional scalar payload round-trip.
- optional scalar payload round-trip

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c28b3dd95047389080682b3563d2c5ba2371c652a93e8f15738a70fb8f2ae4cc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c28b3dd95047389080682b3563d2c5ba2371c652a93e8f15738a70fb8f2ae4cc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c28b3dd95047389080682b3563d2c5ba2371c652a93e8f15738a70fb8f2ae4cc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/optional_scalar_payload_roundtrip_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/optional_scalar_payload_roundtrip_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/optional_scalar_payload_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/optional_scalar_payload_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/optional_scalar_payload_roundtrip_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders an i64 optional bound from a literal as its payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/optional_scalar_payload_roundtrip_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unwraps a non-nil optional to its payload instead of nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/optional_scalar_payload_roundtrip_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the payload from `??` and reaches the default only on nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
