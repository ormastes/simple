# Memory Capabilities Specification

> Tests covering Memory Capabilities.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Memory Capabilities Specification

## Scenarios

### Memory Capabilities

#### RefCapability

#### maps to Lean names

- maps to Lean names
   - Expected: caps.RefCapability.Imm.to_lean_name() equals `Shared`
   - Expected: caps.RefCapability.Mut.to_lean_name() equals `Exclusive`
   - Expected: caps.RefCapability.Iso.to_lean_name() equals `Isolated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps to Lean names")
expect(caps.RefCapability.Imm.to_lean_name()).to_equal("Shared")
expect(caps.RefCapability.Mut.to_lean_name()).to_equal("Exclusive")
expect(caps.RefCapability.Iso.to_lean_name()).to_equal("Isolated")
```

</details>

#### checks mutation and aliasing rules

- checks mutation and aliasing rules
   - Expected: caps.RefCapability.Mut.allows_mutation() is true
   - Expected: caps.RefCapability.Imm.allows_mutation() is false
   - Expected: caps.RefCapability.Imm.allows_aliasing() is true
   - Expected: caps.RefCapability.Mut.allows_aliasing() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks mutation and aliasing rules")
expect(caps.RefCapability.Mut.allows_mutation()).to_equal(true)
expect(caps.RefCapability.Imm.allows_mutation()).to_equal(false)
expect(caps.RefCapability.Imm.allows_aliasing()).to_equal(true)
expect(caps.RefCapability.Mut.allows_aliasing()).to_equal(false)
```

</details>

#### CapType

#### builds Lean syntax

- builds Lean syntax
   - Expected: caps.CapType.imm_type("Int").to_lean() equals `CapType.mk "Int" RefCapability.Shared`
   - Expected: caps.CapType.mut_type("Int").to_lean() equals `CapType.mk "Int" RefCapability.Exclusive`
   - Expected: caps.CapType.iso_type("Int").to_lean() equals `CapType.mk "Int" RefCapability.Isolated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds Lean syntax")
expect(caps.CapType.imm_type("Int").to_lean()).to_equal("CapType.mk \"Int\" RefCapability.Shared")
expect(caps.CapType.mut_type("Int").to_lean()).to_equal("CapType.mk \"Int\" RefCapability.Exclusive")
expect(caps.CapType.iso_type("Int").to_lean()).to_equal("CapType.mk \"Int\" RefCapability.Isolated")
```

</details>

#### RefEnv

#### stores and consumes references

- stores and consumes references
   - Expected: env.is_available("x") is true
   - Expected: env.is_available("x") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores and consumes references")
var env = caps.RefEnv.new()
env.add("x", caps.CapType.imm_type("Int"))

expect(env.is_available("x")).to_equal(true)
val _ = env.consume("x")
expect(env.is_available("x")).to_equal(false)
```

</details>

#### returns the stored reference

- returns the stored reference
   - Expected: env.get("y") != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the stored reference")
var env = caps.RefEnv.new()
env.add("y", caps.CapType.iso_type("Nat"))
expect(env.get("y") != nil).to_equal(true)
```

</details>

#### Conversion rules

#### accepts the documented capability transitions

- accepts the documented capability transitions
   - Expected: caps.can_convert(caps.RefCapability.Mut, caps.RefCapability.Mut) is true
   - Expected: caps.can_convert(caps.RefCapability.Mut, caps.RefCapability.Imm) is true
   - Expected: caps.can_convert(caps.RefCapability.Iso, caps.RefCapability.Mut) is true
   - Expected: caps.can_convert(caps.RefCapability.Iso, caps.RefCapability.Imm) is true
   - Expected: caps.can_convert(caps.RefCapability.Imm, caps.RefCapability.Mut) is false
   - Expected: caps.can_convert(caps.RefCapability.Imm, caps.RefCapability.Iso) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the documented capability transitions")
expect(caps.can_convert(caps.RefCapability.Mut, caps.RefCapability.Mut)).to_equal(true)
expect(caps.can_convert(caps.RefCapability.Mut, caps.RefCapability.Imm)).to_equal(true)
expect(caps.can_convert(caps.RefCapability.Iso, caps.RefCapability.Mut)).to_equal(true)
expect(caps.can_convert(caps.RefCapability.Iso, caps.RefCapability.Imm)).to_equal(true)
expect(caps.can_convert(caps.RefCapability.Imm, caps.RefCapability.Mut)).to_equal(false)
expect(caps.can_convert(caps.RefCapability.Imm, caps.RefCapability.Iso)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/verification/memory_capabilities_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Memory Capabilities.
- Memory Capabilities

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `b8743368e17b83f514a7faf9efc7bfa9503062a7ceee215cb2bbb01dd9b13b97`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b8743368e17b83f514a7faf9efc7bfa9503062a7ceee215cb2bbb01dd9b13b97`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b8743368e17b83f514a7faf9efc7bfa9503062a7ceee215cb2bbb01dd9b13b97`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/verification/memory_capabilities_spec.spl
mirror: doc/06_spec/unit/compiler/verification/memory_capabilities_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/verification/memory_capabilities_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/verification/memory_capabilities_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/verification/memory_capabilities_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps to Lean names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/verification/memory_capabilities_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks mutation and aliasing rules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/verification/memory_capabilities_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds Lean syntax' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
