# Inline Asm Output Writeback Specification

> Tests covering Inline asm MIR lowering writes outputs back.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inline Asm Output Writeback Specification

## Scenarios

### Inline asm MIR lowering writes outputs back

#### reads a non-empty lowering source (non-vacuity control)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads a non-empty lowering source (non-vacuity control)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads a non-empty lowering source (non-vacuity control)")
# Without this, a moved/renamed file would make every assertion below
# pass against the empty string.
val src = lowering_source()
expect(src.len() > 2000).to_be(true)
expect(src.contains("me lower_inline_asm(asm_node: HirAsm)")).to_be(true)
```

</details>

#### allocates a FRESH temp per output instead of aliasing the source local

- allocates a FRESH temp per output instead of aliasing the source local


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates a FRESH temp per output instead of aliasing the source local")
# The defect was `operand: mir_operand_copy(value_local)` on the output
# side: the output and its own source were the same local, so LLVM's
# `=r` result had nowhere to land.
val src = lowering_source()
expect(src.contains("var output_destinations: [LocalId] = []")).to_be(true)
expect(src.contains("var output_results: [LocalId] = []")).to_be(true)
expect(src.contains("val output_temp = self.builder.new_temp(")).to_be(true)
```

</details>

#### emits an explicit Copy write-back for every recorded output

- emits an explicit Copy write-back for every recorded output


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits an explicit Copy write-back for every recorded output")
val src = lowering_source()
expect(src.contains(
    "kind: MirInstKind.Copy(output_destinations[writeback_index], output_results[writeback_index])"
)).to_be(true)
expect(src.contains("while writeback_index < output_destinations.len():")).to_be(true)
```

</details>

#### records a destination for EVERY output constraint kind (class guard)

- records a destination for EVERY output constraint kind (class guard)
   - Expected: src.count("output_destinations.push(") equals `src.count("output_results.push(")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records a destination for EVERY output constraint kind (class guard)")
# Out / LateOut and InOut are the two output-bearing arms today. Each
# must push BOTH a destination and a result, or its write-back is
# silently skipped. Counting the pushes catches a third arm added later
# that forgets one half of the pair.
val src = lowering_source()
expect(src.count("output_destinations.push(")).to_equal(src.count("output_results.push("))
expect(src.count("output_destinations.push(") >= 2).to_be(true)
expect(src.contains("case Out | LateOut:")).to_be(true)
expect(src.contains("case InOut:")).to_be(true)
```

</details>

#### keeps the LLVM backend consuming the output operands it is handed

- keeps the LLVM backend consuming the output operands it is handed


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the LLVM backend consuming the output operands it is handed")
# Single-output captures the call result; multi-output must extractvalue
# each field. Dropping either half reintroduces the silent zero.
val backend = read_file_text(
    "src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl"
)
expect(backend.len() > 2000).to_be(true)
expect(backend.contains("me translate_inline_asm(")).to_be(true)
expect(backend.contains("extractvalue")).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/inline_asm_output_writeback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Inline asm MIR lowering writes outputs back.
- Inline asm MIR lowering writes outputs back

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `be20720e36943fce1916b6a66bd7a1d027797188baf60f0023ba73c346e9a81b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `be20720e36943fce1916b6a66bd7a1d027797188baf60f0023ba73c346e9a81b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `be20720e36943fce1916b6a66bd7a1d027797188baf60f0023ba73c346e9a81b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir/inline_asm_output_writeback_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/inline_asm_output_writeback_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/inline_asm_output_writeback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/inline_asm_output_writeback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/inline_asm_output_writeback_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a non-empty lowering source (non-vacuity control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/inline_asm_output_writeback_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates a FRESH temp per output instead of aliasing the source local' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/inline_asm_output_writeback_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits an explicit Copy write-back for every recorded output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
