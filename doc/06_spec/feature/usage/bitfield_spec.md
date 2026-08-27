# Bitfield Feature Plan

> Tests the bitfield feature plan by verifying parser phase scope, validation phase scope, and coverage path tracking. Ensures the bitfield declaration syntax, storage widths, field widths, and reserved field support are properly scoped and linked to the canonical implementation plan.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bitfield Feature Plan

Tests the bitfield feature plan by verifying parser phase scope, validation phase scope, and coverage path tracking. Ensures the bitfield declaration syntax, storage widths, field widths, and reserved field support are properly scoped and linked to the canonical implementation plan.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | In Progress |
| Source | `test/feature/usage/bitfield_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the bitfield feature plan by verifying parser phase scope, validation phase scope,
and coverage path tracking. Ensures the bitfield declaration syntax, storage widths,
field widths, and reserved field support are properly scoped and linked to the
canonical implementation plan.

## Scenarios

### Bitfield Feature Plan

#### locks parser phase scope

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- locks parser phase scope
- locks parser phase scope
   - Expected: count_texts(PARSER_PHASE) equals `3`
   - Expected: has_text(PARSER_PHASE, "keyword: bitfield") is true
   - Expected: has_text(PARSER_PHASE, "declaration syntax: bitfield Name(BackingType):") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("locks parser phase scope")
step("locks parser phase scope")
# @req: REQ-FEAT-USAGE-BITFIELD-SPEC-001
expect(count_texts(PARSER_PHASE)).to_equal(3)
expect(has_text(PARSER_PHASE, "keyword: bitfield")).to_equal(true)
expect(has_text(PARSER_PHASE, "declaration syntax: bitfield Name(BackingType):")).to_equal(true)
```

</details>

#### locks validation phase scope

- locks validation phase scope
- locks validation phase scope
   - Expected: count_texts(VALIDATION_PHASE) equals `3`
   - Expected: has_text(VALIDATION_PHASE, "storage widths: u8/u16/u32/u64") is true
   - Expected: has_text(VALIDATION_PHASE, "reserved fields: _") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("locks validation phase scope")
step("locks validation phase scope")
expect(count_texts(VALIDATION_PHASE)).to_equal(3)
expect(has_text(VALIDATION_PHASE, "storage widths: u8/u16/u32/u64")).to_equal(true)
expect(has_text(VALIDATION_PHASE, "reserved fields: _")).to_equal(true)
```

</details>

#### links to canonical implementation plan

- links to canonical implementation plan
- links to canonical implementation plan
   - Expected: count_texts(docs) equals `1`
   - Expected: has_text(docs, "doc/03_plan/bitfield_feature_plan_2026-02-24.md") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("links to canonical implementation plan")
step("links to canonical implementation plan")
val docs = ["doc/03_plan/bitfield_feature_plan_2026-02-24.md"]
expect(count_texts(docs)).to_equal(1)
expect(has_text(docs, "doc/03_plan/bitfield_feature_plan_2026-02-24.md")).to_equal(true)
```

</details>

#### tracks executable coverage paths

- tracks executable coverage paths
- tracks executable coverage paths
   - Expected: count_texts(COVERAGE_PATHS) equals `6`
   - Expected: has_text(COVERAGE_PATHS, "test/feature/usage/bitfield_runtime_compat_spec.spl") is true
   - Expected: has_text(COVERAGE_PATHS, "test/unit/compiler/parser/bitfield_pure_simple_spec.spl") is true
   - Expected: has_text(COVERAGE_PATHS, "test/unit/compiler/native/bitfield_codegen_spec.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tracks executable coverage paths")
step("tracks executable coverage paths")
expect(count_texts(COVERAGE_PATHS)).to_equal(6)
expect(has_text(COVERAGE_PATHS, "test/feature/usage/bitfield_runtime_compat_spec.spl")).to_equal(true)
expect(has_text(COVERAGE_PATHS, "test/unit/compiler/parser/bitfield_pure_simple_spec.spl")).to_equal(true)
expect(has_text(COVERAGE_PATHS, "test/unit/compiler/native/bitfield_codegen_spec.spl")).to_equal(true)
```

</details>

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

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-USAGE-BITFIELD-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b5dd19aec9044c428b8bd3e449baa59a0063821e27118666a859b3234099e93d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b5dd19aec9044c428b8bd3e449baa59a0063821e27118666a859b3234099e93d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b5dd19aec9044c428b8bd3e449baa59a0063821e27118666a859b3234099e93d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/usage/bitfield_spec.spl
mirror: doc/06_spec/feature/usage/bitfield_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/bitfield_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/bitfield_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/bitfield_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/bitfield_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'locks parser phase scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/bitfield_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'locks validation phase scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/bitfield_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'links to canonical implementation plan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
