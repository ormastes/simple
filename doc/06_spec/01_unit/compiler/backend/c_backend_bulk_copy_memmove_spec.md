# C Backend Bulk Copy Memmove Specification

> Tests covering C backend lowers active bulk_copy to memmove (SG-1.3).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# C Backend Bulk Copy Memmove Specification

## Scenarios

### C backend lowers active bulk_copy to memmove (SG-1.3)

#### emits a memmove for bulk_copy

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits a memmove for bulk_copy
   - Expected: _emit_inst(_bulk_copy()) contains `memmove(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a memmove for bulk_copy")
expect(_emit_inst(_bulk_copy()).contains("memmove(")).to_equal(true)
```

</details>

#### memmove byte length is count * 8 (element stride)

- memmove byte length is count * 8 (element stride)
   - Expected: _emit_inst(_bulk_copy()) contains `) * 8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("memmove byte length is count * 8 (element stride)")
expect(_emit_inst(_bulk_copy()).contains(") * 8")).to_equal(true)
```

</details>

#### memmove arg order is (dst, src, n) — dst first, src second

- memmove arg order is (dst, src, n) — dst first, src second
   - Expected: _emit_inst(_bulk_copy()) contains `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("memmove arg order is (dst, src, n) — dst first, src second")
val dst_name = _operand_text(_copy(20))
val src_name = _operand_text(_copy(10))
val expected = "memmove((void*)" + dst_name + ", (void*)" + src_name + ", "
expect(_emit_inst(_bulk_copy()).contains(expected)).to_equal(true)
```

</details>

#### false-green guard: a non-bulk intrinsic still emits __simple_intrinsic_

- false-green guard: a non-bulk intrinsic still emits __simple_intrinsic_
   - Expected: out contains `__simple_intrinsic_some_other`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("false-green guard: a non-bulk intrinsic still emits __simple_intrinsic_")
val out = _emit_inst(MirInst(kind: MirInstKind.Intrinsic(nil, "some_other", [_copy(10)]), span: nil))
expect(out.contains("__simple_intrinsic_some_other")).to_equal(true)
```

</details>

#### no-op hint path is untouched: emits no memmove (back-compat)

- no-op hint path is untouched: emits no memmove (back-compat)
   - Expected: out does not contain `memmove(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no-op hint path is untouched: emits no memmove (back-compat)")
val out = _emit_inst(MirInst(kind: MirInstKind.Intrinsic(nil, "bulk_copy_hint", [_copy(10), _copy(20), _const(4)]), span: nil))
expect(out.contains("memmove(")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/c_backend_bulk_copy_memmove_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering C backend lowers active bulk_copy to memmove (SG-1.3).
- C backend lowers active bulk_copy to memmove (SG-1.3)

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

- Canonical SPipe generation for source `6e20d7dae81b415d4bfa084130b7af9abaee221cca27b7d69bde506c83c6b4da`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6e20d7dae81b415d4bfa084130b7af9abaee221cca27b7d69bde506c83c6b4da`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6e20d7dae81b415d4bfa084130b7af9abaee221cca27b7d69bde506c83c6b4da`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/c_backend_bulk_copy_memmove_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/c_backend_bulk_copy_memmove_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/c_backend_bulk_copy_memmove_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/c_backend_bulk_copy_memmove_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/c_backend_bulk_copy_memmove_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a memmove for bulk_copy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/c_backend_bulk_copy_memmove_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'memmove byte length is count * 8 (element stride)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/c_backend_bulk_copy_memmove_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'memmove arg order is (dst, src, n) — dst first, src second' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
