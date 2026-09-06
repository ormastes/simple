# Attributes Specification

> Tests covering FunctionAttr, parse_function_attrs, VHDL clock metadata.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Attributes Specification

## Scenarios

### FunctionAttr

### parse_function_attrs

#### parses bare fast_math

- parses bare fast_math
   - Expected: fa.has_fast_math is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses bare fast_math")
val fa = parse_function_attrs([make_attr("fast_math")])
expect(fa.has_fast_math).to_equal(true)
```

</details>

#### parses bare simd as enabled

- parses bare simd as enabled
   - Expected: fa.is_simd is true
   - Expected: fa.simd_enable is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses bare simd as enabled")
val fa = parse_function_attrs([make_attr("simd")])
expect(fa.is_simd).to_equal(true)
expect(fa.simd_enable).to_equal(true)
```

</details>

#### parses simd(disable)

- parses simd(disable)
   - Expected: fa.is_simd is true
   - Expected: fa.simd_disable is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simd(disable)")
val fa = parse_function_attrs([make_simd_attr("disable")])
expect(fa.is_simd).to_equal(true)
expect(fa.simd_disable).to_equal(true)
```

</details>

#### parses simd(prefer_scalable)

- parses simd(prefer_scalable)
   - Expected: fa.is_simd is true
   - Expected: fa.simd_prefer_scalable is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simd(prefer_scalable)")
val fa = parse_function_attrs([make_simd_attr("prefer_scalable")])
expect(fa.is_simd).to_equal(true)
expect(fa.simd_prefer_scalable).to_equal(true)
```

</details>

#### default function attrs leave fast_math false

- default function attrs leave fast_math false
   - Expected: fa.has_fast_math is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default function attrs leave fast_math false")
val fa = FunctionAttr.default()
expect(fa.has_fast_math).to_equal(false)
```

</details>

#### parses GPU target metadata from gpu attribute

- parses GPU target metadata from gpu attribute
   - Expected: fa.is_gpu_kernel is true
   - Expected: fa.gpu_target equals `opencl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses GPU target metadata from gpu attribute")
val fa = parse_function_attrs([make_gpu_target_attr("opencl")])
expect(fa.is_gpu_kernel).to_equal(true)
expect(fa.gpu_target).to_equal("opencl")
```

</details>

#### parses GPU backend ordering metadata

- parses GPU backend ordering metadata
   - Expected: fa.is_gpu_kernel is true
   - Expected: fa.gpu_backends equals `cuda,opencl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses GPU backend ordering metadata")
val fa = parse_function_attrs([make_gpu_backends_attr("cuda,opencl")])
expect(fa.is_gpu_kernel).to_equal(true)
expect(fa.gpu_backends).to_equal("cuda,opencl")
```

</details>

### VHDL clock metadata

#### treats positional none as source-owned reset

- treats positional none as source-owned reset
   - Expected: clocked.is_valid is true
   - Expected: clocked.clock_signal equals `clk`
   - Expected: clocked.has_reset is false
   - Expected: clocked.reset_signal equals ``
   - Expected: clocked.reset_synchrony equals `VhdlResetSynchrony.None_`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats positional none as source-owned reset")
val clocked = _parse_vhdl_clocked_args([
    make_ident_expr("clk"), make_ident_expr("none")
])
expect(clocked.is_valid).to_equal(true)
expect(clocked.clock_signal).to_equal("clk")
expect(clocked.has_reset).to_equal(false)
expect(clocked.reset_signal).to_equal("")
expect(clocked.reset_synchrony).to_equal(VhdlResetSynchrony.None_)
```

</details>

#### keeps real positional reset signals backend-managed

- keeps real positional reset signals backend-managed
   - Expected: clocked.is_valid is true
   - Expected: clocked.has_reset is true
   - Expected: clocked.reset_signal equals `reset_n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps real positional reset signals backend-managed")
val clocked = _parse_vhdl_clocked_args([
    make_ident_expr("clk"), make_ident_expr("reset_n")
])
expect(clocked.is_valid).to_equal(true)
expect(clocked.has_reset).to_equal(true)
expect(clocked.reset_signal).to_equal("reset_n")
```

</details>

#### rejects reset synchrony after positional none

- rejects reset synchrony after positional none
   - Expected: clocked.is_valid is false
   - Expected: clocked.has_reset is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects reset synchrony after positional none")
val clocked = _parse_vhdl_clocked_args([
    make_ident_expr("clk"), make_ident_expr("none"),
    make_ident_expr("async")
])
expect(clocked.is_valid).to_equal(false)
expect(clocked.has_reset).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/common/attributes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FunctionAttr, parse_function_attrs, VHDL clock metadata.
- FunctionAttr
- parse_function_attrs
- VHDL clock metadata

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `e743ba7ce59b8f7fc23b1619c7cdc916159a3e44322741317deeac9395257813`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e743ba7ce59b8f7fc23b1619c7cdc916159a3e44322741317deeac9395257813`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e743ba7ce59b8f7fc23b1619c7cdc916159a3e44322741317deeac9395257813`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/common/attributes_spec.spl
mirror: doc/06_spec/01_unit/compiler/common/attributes_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/common/attributes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/common/attributes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/common/attributes_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses bare fast_math' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/common/attributes_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses bare simd as enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/common/attributes_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses simd(disable)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
