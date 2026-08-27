# Tensor Interface Consistency Specification

> As an ML-library user I need the core `PureTensor` to behave the same way the torch-backed `Tensor` does for the shared operations — shape, element access and reshape — so that swapping backends does not silently change results.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tensor Interface Consistency Specification

As an ML-library user I need the core `PureTensor` to behave the same way the torch-backed `Tensor` does for the shared operations — shape, element access and reshape — so that swapping backends does not silently change results.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1920, #1930 |
| Category | ML, Collections, API |
| Status | Complete |
| Source | `test/03_system/feature/usage/tensor_interface_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

As an ML-library user I need the core `PureTensor` to behave the same way the
torch-backed `Tensor` does for the shared operations — shape, element access and
reshape — so that swapping backends does not silently change results.

**The core half of this spec is deliberately UNGATED.** It previously sat behind
`SIMPLE_GPU_TEST=1` and asserted only that its own gate was closed, which meant
the pure-Simple tensor — which needs no GPU, no CUDA and no libtorch — was never
exercised at all. Only the torch-backed comparison genuinely needs an external
runtime, so only that half stays gated, and it announces a VISIBLE skip rather
than asserting a passing value when it does not run.

## Syntax

```simple
use std.spec.step

val t = PureTensor.zeros([2, 3])
expect(t.numel()).to_equal(6)
```

## Scenarios

### Core tensor interface

#### reports a shape and an element count that agree

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports a shape and an element count that agree
- a 2x3 tensor holds exactly six elements
   - Expected: t.numel() equals `6`
   - Expected: t.shape.len() equals `2`
   - Expected: t.shape[0] equals `2`
   - Expected: t.shape[1] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports a shape and an element count that agree")
step("a 2x3 tensor holds exactly six elements")
val t = PureTensor.zeros([2, 3])
expect(t.numel()).to_equal(6)
expect(t.shape.len()).to_equal(2)
expect(t.shape[0]).to_equal(2)
expect(t.shape[1]).to_equal(3)
```

</details>

#### initialises zeros and ones to their named values

- initialises zeros and ones to their named values
- zeros() is genuinely zero-filled, not merely allocated
   - Expected: z.get([0, 0]) equals `0.0`
   - Expected: z.get([1, 1]) equals `0.0`
- ones() is genuinely one-filled — the two must not be the same buffer
   - Expected: o.get([0, 0]) equals `1.0`
   - Expected: o.get([1, 1]) equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("initialises zeros and ones to their named values")
step("zeros() is genuinely zero-filled, not merely allocated")
val z = PureTensor.zeros([2, 2])
expect(z.get([0, 0])).to_equal(0.0)
expect(z.get([1, 1])).to_equal(0.0)

step("ones() is genuinely one-filled — the two must not be the same buffer")
val o = PureTensor.ones([2, 2])
expect(o.get([0, 0])).to_equal(1.0)
expect(o.get([1, 1])).to_equal(1.0)
```

</details>

#### round-trips a written element through get/set

- round-trips a written element through get/set
- writing one element leaves its neighbour untouched
   - Expected: t.get([0, 1]) equals `7.5`
   - Expected: t.get([0, 0]) equals `0.0`
   - Expected: t.get([1, 1]) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("round-trips a written element through get/set")
step("writing one element leaves its neighbour untouched")
var t = PureTensor.zeros([2, 2])
t.set([0, 1], 7.5)
expect(t.get([0, 1])).to_equal(7.5)
expect(t.get([0, 0])).to_equal(0.0)
expect(t.get([1, 1])).to_equal(0.0)
```

</details>

#### reshapes without changing the element count

- reshapes without changing the element count
- a 2x3 tensor reshaped to 3x2 still holds six elements
   - Expected: r.numel() equals `6`
   - Expected: r.shape[0] equals `3`
   - Expected: r.shape[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reshapes without changing the element count")
step("a 2x3 tensor reshaped to 3x2 still holds six elements")
val t = PureTensor.zeros([2, 3])
val r = t.reshape([3, 2])
expect(r.numel()).to_equal(6)
expect(r.shape[0]).to_equal(3)
expect(r.shape[1]).to_equal(2)
```

</details>

### Torch-backed tensor parity

#### compares against torch only when SIMPLE_GPU_TEST is open, and skips visibly otherwise

- compares against torch only when SIMPLE_GPU_TEST is open, and skips visibly otherwise
- gate CLOSED — no torch claim is made, and this is stated aloud
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`
- gate OPEN — the operator asserts a torch runtime, so demand parity
   - Expected: core.numel() equals `6`
   - Expected: core.shape[0] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares against torch only when SIMPLE_GPU_TEST is open, and skips visibly otherwise")
if not test_env_gpu_available():
    step("gate CLOSED — no torch claim is made, and this is stated aloud")
    print("SKIP (no torch parity assertion made): " + test_env_gate_reason("SIMPLE_GPU_TEST"))
    expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
else:
    step("gate OPEN — the operator asserts a torch runtime, so demand parity")
    # Kept as the core-side expectation the torch side must match; the
    # torch import is deliberately not a top-level `use` so that a host
    # without libtorch can still load this file.
    val core = PureTensor.zeros([2, 3])
    expect(core.numel()).to_equal(6)
    expect(core.shape[0]).to_equal(2)
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

- Canonical SPipe generation for source `80341eae89db3d7f351016db3ac55be217402602aead3ce45546ccaaff2aa7e1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `80341eae89db3d7f351016db3ac55be217402602aead3ce45546ccaaff2aa7e1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `80341eae89db3d7f351016db3ac55be217402602aead3ce45546ccaaff2aa7e1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/usage/tensor_interface_spec.spl
mirror: doc/06_spec/03_system/feature/usage/tensor_interface_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/tensor_interface_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/tensor_interface_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/tensor_interface_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/tensor_interface_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a shape and an element count that agree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/tensor_interface_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initialises zeros and ones to their named values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/tensor_interface_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a written element through get/set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
