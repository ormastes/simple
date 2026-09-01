# Handled Variants Neighbour Specification

> Tests covering MIR lowering keeps the 17 previously-handled HirTypeKind arms unchanged.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Handled Variants Neighbour Specification

## Scenarios

### MIR lowering keeps the 17 previously-handled HirTypeKind arms unchanged

#### snapshots the MIR type produced by each already-supported variant

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- snapshots the MIR type produced by each already-supported variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("snapshots the MIR type produced by each already-supported variant")
val source = file_read("src/compiler/50.mir/_MirLowering/function_lowering.spl")
# Int/Float widths -> sized MIR scalars
expect(source).to_contain("case HirTypeKind.Int(bits, signed):")
expect(source).to_contain("case 8: MirType(kind: MirTypeKind.I8)")
expect(source).to_contain("case 8: MirType(kind: MirTypeKind.U8)")
expect(source).to_contain("case HirTypeKind.Float(bits):")
expect(source).to_contain("case 32: MirType(kind: MirTypeKind.F32)")
expect(source).to_contain("case HirTypeKind.Bool:")
expect(source).to_contain("case HirTypeKind.Char:")
expect(source).to_contain("MirType(kind: MirTypeKind.Char)")
# Str stays a (ptr, len) fat pointer
expect(source).to_contain("case HirTypeKind.Str:")
expect(source).to_contain("MirType(kind: MirTypeKind.Ptr(MirType(kind: MirTypeKind.U8), false)),")
expect(source).to_contain("case HirTypeKind.Unit:")
expect(source).to_contain("MirType(kind: MirTypeKind.Unit)")
expect(source).to_contain("case HirTypeKind.Tuple(elements):")
expect(source).to_contain("MirType(kind: MirTypeKind.Tuple(mir_elements))")
expect(source).to_contain("case HirTypeKind.Array(element, size):")
expect(source).to_contain("MirType(kind: MirTypeKind.Array(self.lower_type(element), array_size))")
expect(source).to_contain("case HirTypeKind.Dict(key, value):")
expect(source).to_contain("MirType(kind: MirTypeKind.Dict(self.lower_type(key), self.lower_type(value)))")
expect(source).to_contain("case HirTypeKind.Ref(inner, mutable):")
expect(source).to_contain("MirType(kind: MirTypeKind.Ref(self.lower_type(inner), mutable))")
expect(source).to_contain("case HirTypeKind.Ptr(inner, mutable):")
expect(source).to_contain("MirType.ptr(self.lower_type(inner), mutable)")
# Optional stays (has_value, T)
expect(source).to_contain("case HirTypeKind.Optional(inner):")
expect(source).to_contain("MirType(kind: MirTypeKind.Bool),  # has_value")
expect(source).to_contain("case HirTypeKind.Result(ok_type, err_type):")
expect(source).to_contain("MirType.result(self.lower_type(ok_type), self.lower_type(err_type))")
expect(source).to_contain("case HirTypeKind.Union(members):")
expect(source).to_contain("MirType(kind: MirTypeKind.Union(mir_members))")
expect(source).to_contain("case HirTypeKind.Named(symbol, _):")
expect(source).to_contain("self.canonical_mir_type_symbol(symbol)))")
expect(source).to_contain("case HirTypeKind.Infer(id, generation):")
expect(source).to_contain("unsupported MIR type kind [infer-arm]")
expect(source).to_contain("case HirTypeKind.Never:")
expect(source).to_contain("MirType(kind: MirTypeKind.Never)")
expect(source).to_contain("case HirTypeKind.Error:")
expect(source).to_contain("MirType.i64()")
```

</details>

#### has no undifferentiated fatal wildcard left in lower_type

- has no undifferentiated fatal wildcard left in lower_type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has no undifferentiated fatal wildcard left in lower_type")
val source = file_read("src/compiler/50.mir/_MirLowering/function_lowering.spl")
expect(source).to_contain("me unreachable_hir_type_kind(type_: HirType) -> MirType:")
expect(source.contains("unsupported MIR type kind [wildcard-arm]")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/hir_type_coverage/handled_variants_neighbour_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR lowering keeps the 17 previously-handled HirTypeKind arms unchanged.
- MIR lowering keeps the 17 previously-handled HirTypeKind arms unchanged

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c49c5382a389782697f3f20535396c9dbc62c074f1207a1ffa3c6b4ecaa13ff4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c49c5382a389782697f3f20535396c9dbc62c074f1207a1ffa3c6b4ecaa13ff4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c49c5382a389782697f3f20535396c9dbc62c074f1207a1ffa3c6b4ecaa13ff4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/mir/hir_type_coverage/handled_variants_neighbour_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/hir_type_coverage/handled_variants_neighbour_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/mir/hir_type_coverage/handled_variants_neighbour_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/hir_type_coverage/handled_variants_neighbour_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/hir_type_coverage/handled_variants_neighbour_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/mir/hir_type_coverage/handled_variants_neighbour_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/mir/hir_type_coverage/handled_variants_neighbour_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'snapshots the MIR type produced by each already-supported variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/hir_type_coverage/handled_variants_neighbour_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has no undifferentiated fatal wildcard left in lower_type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
