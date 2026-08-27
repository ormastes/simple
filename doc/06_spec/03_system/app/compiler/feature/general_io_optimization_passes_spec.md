# General Io Optimization Passes Specification

> Tests covering CLibParityHotspot Provider Registration, bulk_copy provider, bulk_fill provider, bulk_cmp provider, endian_load provider, endian_store provider, Provider Generality, Provider Fact Gating.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# General Io Optimization Passes Specification

## Scenarios

### CLibParityHotspot Provider Registration

### bulk_copy provider

#### has CLibParityHotspot kind

- has CLibParityHotspot kind
   - Expected: p.kind equals `OptimizerProviderKind.CLibParityHotspot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has CLibParityHotspot kind")
val p = optimization_rule_provider_bulk_copy("simple.opt.mir.bulk_copy")
expect(p.kind).to_equal(OptimizerProviderKind.CLibParityHotspot)
```

</details>

#### is hot_path and enabled

- is hot_path and enabled
   - Expected: p.hot_path is true
   - Expected: p.enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is hot_path and enabled")
val p = optimization_rule_provider_bulk_copy("simple.opt.mir.bulk_copy")
expect(p.hot_path).to_equal(true)
expect(p.enabled).to_equal(true)
```

</details>

#### uses PipelinePass lookup

- uses PipelinePass lookup
   - Expected: p.lookup_kind equals `OptimizerRuleLookupKind.PipelinePass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses PipelinePass lookup")
val p = optimization_rule_provider_bulk_copy("simple.opt.mir.bulk_copy")
expect(p.lookup_kind).to_equal(OptimizerRuleLookupKind.PipelinePass)
```

</details>

#### produces bulk_copy_rewrite fact

- produces bulk_copy_rewrite fact


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces bulk_copy_rewrite fact")
val p = optimization_rule_provider_bulk_copy("simple.opt.mir.bulk_copy")
expect(p.produced_facts.len()).to_be_greater_than(0)
```

</details>

### bulk_fill provider

#### has CLibParityHotspot kind

- has CLibParityHotspot kind
   - Expected: p.kind equals `OptimizerProviderKind.CLibParityHotspot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has CLibParityHotspot kind")
val p = optimization_rule_provider_bulk_fill("simple.opt.mir.bulk_fill")
expect(p.kind).to_equal(OptimizerProviderKind.CLibParityHotspot)
```

</details>

#### is hot_path and enabled

- is hot_path and enabled
   - Expected: p.hot_path is true
   - Expected: p.enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is hot_path and enabled")
val p = optimization_rule_provider_bulk_fill("simple.opt.mir.bulk_fill")
expect(p.hot_path).to_equal(true)
expect(p.enabled).to_equal(true)
```

</details>

### bulk_cmp provider

#### has CLibParityHotspot kind

- has CLibParityHotspot kind
   - Expected: p.kind equals `OptimizerProviderKind.CLibParityHotspot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has CLibParityHotspot kind")
val p = optimization_rule_provider_bulk_cmp("simple.opt.mir.bulk_cmp")
expect(p.kind).to_equal(OptimizerProviderKind.CLibParityHotspot)
```

</details>

#### is hot_path and enabled

- is hot_path and enabled
   - Expected: p.hot_path is true
   - Expected: p.enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is hot_path and enabled")
val p = optimization_rule_provider_bulk_cmp("simple.opt.mir.bulk_cmp")
expect(p.hot_path).to_equal(true)
expect(p.enabled).to_equal(true)
```

</details>

### endian_load provider

#### has CLibParityHotspot kind

- has CLibParityHotspot kind
   - Expected: p.kind equals `OptimizerProviderKind.CLibParityHotspot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has CLibParityHotspot kind")
val p = optimization_rule_provider_endian_load("simple.opt.mir.endian_load")
expect(p.kind).to_equal(OptimizerProviderKind.CLibParityHotspot)
```

</details>

#### is hot_path and enabled

- is hot_path and enabled
   - Expected: p.hot_path is true
   - Expected: p.enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is hot_path and enabled")
val p = optimization_rule_provider_endian_load("simple.opt.mir.endian_load")
expect(p.hot_path).to_equal(true)
expect(p.enabled).to_equal(true)
```

</details>

### endian_store provider

#### has CLibParityHotspot kind

- has CLibParityHotspot kind
   - Expected: p.kind equals `OptimizerProviderKind.CLibParityHotspot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has CLibParityHotspot kind")
val p = optimization_rule_provider_endian_store("simple.opt.mir.endian_store")
expect(p.kind).to_equal(OptimizerProviderKind.CLibParityHotspot)
```

</details>

#### is hot_path and enabled

- is hot_path and enabled
   - Expected: p.hot_path is true
   - Expected: p.enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is hot_path and enabled")
val p = optimization_rule_provider_endian_store("simple.opt.mir.endian_store")
expect(p.hot_path).to_equal(true)
expect(p.enabled).to_equal(true)
```

</details>

### Provider Generality

#### bulk_copy requires typed_mir not fs-specific facts

- bulk_copy requires typed_mir not fs-specific facts
   - Expected: p.safety_class equals `pure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bulk_copy requires typed_mir not fs-specific facts")
val p = optimization_rule_provider_bulk_copy("simple.opt.mir.bulk_copy")
expect(p.safety_class).to_equal("pure")
expect(p.required_facts.len()).to_be_greater_than(0)
```

</details>

#### endian_load requires shift_or_chain not fs-specific facts

- endian_load requires shift_or_chain not fs-specific facts
   - Expected: p.safety_class equals `pure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("endian_load requires shift_or_chain not fs-specific facts")
val p = optimization_rule_provider_endian_load("simple.opt.mir.endian_load")
expect(p.safety_class).to_equal("pure")
```

</details>

#### endian_store requires shift_and_store_chain

- endian_store requires shift_and_store_chain
   - Expected: p.safety_class equals `pure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("endian_store requires shift_and_store_chain")
val p = optimization_rule_provider_endian_store("simple.opt.mir.endian_store")
expect(p.safety_class).to_equal("pure")
```

</details>

#### existing clib_parity provider still works

- existing clib_parity provider still works
   - Expected: p.kind equals `OptimizerProviderKind.CLibParityHotspot`
   - Expected: p.hot_path is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("existing clib_parity provider still works")
val p = optimization_rule_provider_clib_parity("simple.opt.mir.clib_parity", true)
expect(p.kind).to_equal(OptimizerProviderKind.CLibParityHotspot)
expect(p.hot_path).to_equal(true)
```

</details>

### Provider Fact Gating

#### bulk_copy can run when required facts are present

- bulk_copy can run when required facts are present
   - Expected: optimization_rule_provider_can_run(p, facts) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bulk_copy can run when required facts are present")
val p = optimization_rule_provider_bulk_copy("simple.opt.mir.bulk_copy")
val facts = ["typed_mir", "gep_contiguous"]
expect(optimization_rule_provider_can_run(p, facts)).to_equal(true)
```

</details>

#### bulk_copy cannot run when facts are missing

- bulk_copy cannot run when facts are missing
   - Expected: optimization_rule_provider_can_run(p, empty_facts) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bulk_copy cannot run when facts are missing")
val p = optimization_rule_provider_bulk_copy("simple.opt.mir.bulk_copy")
val empty_facts: [text] = []
expect(optimization_rule_provider_can_run(p, empty_facts)).to_equal(false)
```

</details>

#### endian_load can run when shift_or_chain fact is present

- endian_load can run when shift_or_chain fact is present
   - Expected: optimization_rule_provider_can_run(p, facts) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("endian_load can run when shift_or_chain fact is present")
val p = optimization_rule_provider_endian_load("simple.opt.mir.endian_load")
val facts = ["typed_mir", "shift_or_chain"]
expect(optimization_rule_provider_can_run(p, facts)).to_equal(true)
```

</details>

#### endian_store cannot run without shift_and_store_chain

- endian_store cannot run without shift_and_store_chain
   - Expected: optimization_rule_provider_can_run(p, facts) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("endian_store cannot run without shift_and_store_chain")
val p = optimization_rule_provider_endian_store("simple.opt.mir.endian_store")
val facts = ["typed_mir"]
expect(optimization_rule_provider_can_run(p, facts)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/general_io_optimization_passes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CLibParityHotspot Provider Registration, bulk_copy provider, bulk_fill provider, bulk_cmp provider, endian_load provider, endian_store provider, Provider Generality, Provider Fact Gating.
- CLibParityHotspot Provider Registration
- bulk_copy provider
- bulk_fill provider
- bulk_cmp provider
- endian_load provider
- endian_store provider
- Provider Generality
- Provider Fact Gating

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `f84f0e13017913ae2b1c07de210c3cfa08eab1bee5730269a1ec43bf6351e342`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f84f0e13017913ae2b1c07de210c3cfa08eab1bee5730269a1ec43bf6351e342`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f84f0e13017913ae2b1c07de210c3cfa08eab1bee5730269a1ec43bf6351e342`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/compiler/feature/general_io_optimization_passes_spec.spl
mirror: doc/06_spec/03_system/app/compiler/feature/general_io_optimization_passes_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/compiler/feature/general_io_optimization_passes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/compiler/feature/general_io_optimization_passes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/compiler/feature/general_io_optimization_passes_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has CLibParityHotspot kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/compiler/feature/general_io_optimization_passes_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is hot_path and enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/compiler/feature/general_io_optimization_passes_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses PipelinePass lookup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
