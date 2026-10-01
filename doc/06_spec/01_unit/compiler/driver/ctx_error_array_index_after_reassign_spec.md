# Ctx Error Array Index After Reassign Specification

> Tests covering array index after struct reassign from a returned value.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ctx Error Array Index After Reassign Specification

## Scenarios

### array index after struct reassign from a returned value

#### reports the same count that indexing can actually reach

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports the same count that indexing can actually reach
   - Expected: n equals `3`
   - Expected: reached.len() equals `3`
   - Expected: reached[0] equals `alpha`
   - Expected: reached[2] equals `gamma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports the same count that indexing can actually reach")
var h = SpecHolder(ctx: SpecCtx(errors: []))
val produced = _make_spec_ctx()
h.ctx = produced
val n = h.ctx.errors.len()
expect(n).to_equal(3)
var reached: [text] = []
var i = 0
while i < n:
    reached.push(h.ctx.errors[i])
    i = i + 1
expect(reached.len()).to_equal(3)
expect(reached[0]).to_equal("alpha")
expect(reached[2]).to_equal("gamma")
```

</details>

#### reads the field through a typed local alias too

- reads the field through a typed local alias too
   - Expected: direct.len() equals `3`
   - Expected: direct[0] equals `alpha`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads the field through a typed local alias too")
var h = SpecHolder(ctx: SpecCtx(errors: []))
h.ctx = _make_spec_ctx()
val direct: [text] = h.ctx.errors
expect(direct.len()).to_equal(3)
expect(direct[0]).to_equal("alpha")
```

</details>

#### reads the field through a method-shaped accessor

- reads the field through a method-shaped accessor
   - Expected: _at(h.ctx, 1) equals `beta`
   - Expected: _at(h.ctx, 99) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads the field through a method-shaped accessor")
# The accessor shape is what driver_types.CompilerContext.error_message_at
# uses, because a method call on the owner was the only shape measured to
# work in the failing Stage-3 binary.
var h = SpecHolder(ctx: SpecCtx(errors: []))
h.ctx = _make_spec_ctx()
expect(_at(h.ctx, 1)).to_equal("beta")
expect(_at(h.ctx, 99)).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/ctx_error_array_index_after_reassign_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering array index after struct reassign from a returned value.
- array index after struct reassign from a returned value

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `02ecf5f5ff8a60fe65af372b590a95d9bc84706e48ed2953bf7234c94741f2d6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `02ecf5f5ff8a60fe65af372b590a95d9bc84706e48ed2953bf7234c94741f2d6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `02ecf5f5ff8a60fe65af372b590a95d9bc84706e48ed2953bf7234c94741f2d6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/driver/ctx_error_array_index_after_reassign_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/ctx_error_array_index_after_reassign_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/ctx_error_array_index_after_reassign_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/ctx_error_array_index_after_reassign_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/ctx_error_array_index_after_reassign_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/ctx_error_array_index_after_reassign_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the same count that indexing can actually reach' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/ctx_error_array_index_after_reassign_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the field through a typed local alias too' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/ctx_error_array_index_after_reassign_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the field through a method-shaped accessor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
