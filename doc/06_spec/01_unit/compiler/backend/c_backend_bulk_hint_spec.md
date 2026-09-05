# C Backend Bulk Hint Specification

> Tests covering C backend drops advisory bulk-op hints (SG-1.3).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# C Backend Bulk Hint Specification

## Scenarios

### C backend drops advisory bulk-op hints (SG-1.3)

#### emits no call for bulk_copy_hint

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits no call for bulk_copy_hint
   - Expected: _emit_intrinsic("bulk_copy_hint") does not contain `__simple_intrinsic_bulk_copy_hint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits no call for bulk_copy_hint")
expect(_emit_intrinsic("bulk_copy_hint").contains("__simple_intrinsic_bulk_copy_hint")).to_equal(false)
```

</details>

#### emits no call for bulk_fill_hint

- emits no call for bulk_fill_hint
   - Expected: _emit_intrinsic("bulk_fill_hint") does not contain `__simple_intrinsic_bulk_fill_hint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits no call for bulk_fill_hint")
expect(_emit_intrinsic("bulk_fill_hint").contains("__simple_intrinsic_bulk_fill_hint")).to_equal(false)
```

</details>

#### emits no call for bulk_cmp_hint

- emits no call for bulk_cmp_hint
   - Expected: _emit_intrinsic("bulk_cmp_hint") does not contain `__simple_intrinsic_bulk_cmp_hint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits no call for bulk_cmp_hint")
expect(_emit_intrinsic("bulk_cmp_hint").contains("__simple_intrinsic_bulk_cmp_hint")).to_equal(false)
```

</details>

#### still emits the call for a non-bulk intrinsic (else path intact / false-green guard)

- still emits the call for a non-bulk intrinsic (else path intact / false-green guard)
   - Expected: _emit_intrinsic("some_other_intrinsic") contains `__simple_intrinsic_some_other_intrinsic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still emits the call for a non-bulk intrinsic (else path intact / false-green guard)")
expect(_emit_intrinsic("some_other_intrinsic").contains("__simple_intrinsic_some_other_intrinsic")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/c_backend_bulk_hint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering C backend drops advisory bulk-op hints (SG-1.3).
- C backend drops advisory bulk-op hints (SG-1.3)

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

- Canonical SPipe generation for source `c34c3729257ff196d62f7542f65c3aafb3f8c109979c39e970ef94c56bbef2de`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c34c3729257ff196d62f7542f65c3aafb3f8c109979c39e970ef94c56bbef2de`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c34c3729257ff196d62f7542f65c3aafb3f8c109979c39e970ef94c56bbef2de`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/c_backend_bulk_hint_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/c_backend_bulk_hint_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/c_backend_bulk_hint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/c_backend_bulk_hint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/c_backend_bulk_hint_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits no call for bulk_copy_hint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/c_backend_bulk_hint_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits no call for bulk_fill_hint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/c_backend_bulk_hint_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits no call for bulk_cmp_hint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
