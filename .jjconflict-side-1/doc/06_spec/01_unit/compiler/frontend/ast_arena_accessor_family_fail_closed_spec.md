# Ast Arena Accessor Family Fail Closed Specification

> Tests covering AST arena accessor family fails closed on every non-live index.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ast Arena Accessor Family Fail Closed Specification

## Scenarios

### AST arena accessor family fails closed on every non-live index

#### answers with absent-sentinels for an index PAST the end of the arena

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- answers with absent-sentinels for an index PAST the end of the arena


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("answers with absent-sentinels for an index PAST the end of the arena")
ast_reset()
stmt_reset()
expect _probe_all(12) to_equal 8
```

</details>

#### answers with absent-sentinels for a NEGATIVE index (the -1 sentinel fed back in)

- answers with absent-sentinels for a NEGATIVE index (the -1 sentinel fed back in)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("answers with absent-sentinels for a NEGATIVE index (the -1 sentinel fed back in)")
ast_reset()
stmt_reset()
expect _probe_all(-1) to_equal 8
```

</details>

#### answers with absent-sentinels for an index stale across a reset

- answers with absent-sentinels for an index stale across a reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("answers with absent-sentinels for an index stale across a reset")
stmt_reset()
val live = stmt_alloc(STMT_EXPR, 7)
ast_reset()
stmt_reset()
expect _probe_all(live + 12) to_equal 8
```

</details>

#### guards the expression half of the family the same way

- guards the expression half of the family the same way


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guards the expression half of the family the same way")
ast_reset()
expect expr_get_tag(-1) to_equal -1
expect expr_get_tag(9999) to_equal -1
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/ast_arena_accessor_family_fail_closed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AST arena accessor family fails closed on every non-live index.
- AST arena accessor family fails closed on every non-live index

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

- Canonical SPipe generation for source `e1aaeb2b5a11b4245a8c1d3b0b98cb526639c9af08a2317219bec4e28c9bbce0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e1aaeb2b5a11b4245a8c1d3b0b98cb526639c9af08a2317219bec4e28c9bbce0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e1aaeb2b5a11b4245a8c1d3b0b98cb526639c9af08a2317219bec4e28c9bbce0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/frontend/ast_arena_accessor_family_fail_closed_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/ast_arena_accessor_family_fail_closed_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/ast_arena_accessor_family_fail_closed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/ast_arena_accessor_family_fail_closed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/ast_arena_accessor_family_fail_closed_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'answers with absent-sentinels for an index PAST the end of the arena' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/ast_arena_accessor_family_fail_closed_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'answers with absent-sentinels for a NEGATIVE index (the -1 sentinel fed back in)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/ast_arena_accessor_family_fail_closed_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'answers with absent-sentinels for an index stale across a reset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
