# Collection Index Mutation Specification

> Tests covering COLL019 mutation through indexed access.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collection Index Mutation Specification

## Scenarios

### COLL019 mutation through indexed access

#### flags a push through a dict-annotated local

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- flags a push through a dict-annotated local
- Lint a function that pushes through a local dict index
   - Expected: coll019_count("/tmp/coll019_local.spl", DICT_SRC) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags a push through a dict-annotated local")
"""`d[\"k\"].push(1)` mutates a copy of the bucket; the dict never
changes. The reader cannot see that, so the lint must."""
step("Lint a function that pushes through a local dict index")
expect(coll019_count("/tmp/coll019_local.spl", DICT_SRC)).to_equal(1)
```

</details>

#### flags a push through a dict-typed parameter

- flags a push through a dict-typed parameter
- Lint a function whose dict evidence is the parameter annotation
   - Expected: coll019_count("/tmp/coll019_param.spl", PARAM_SRC) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags a push through a dict-typed parameter")
step("Lint a function whose dict evidence is the parameter annotation")
expect(coll019_count("/tmp/coll019_param.spl", PARAM_SRC)).to_equal(1)
```

</details>

#### flags a push through a struct field of an indexed element

- flags a push through a struct field of an indexed element
- Lint a push whose receiver is field-of-index
   - Expected: coll019_count("/tmp/coll019_field.spl", FIELD_SRC) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags a push through a struct field of an indexed element")
"""`rows[0].vals.push(5)` is the shape that silently dropped every
group_by member and every CLDR script total."""
step("Lint a push whose receiver is field-of-index")
expect(coll019_count("/tmp/coll019_field.spl", FIELD_SRC)).to_equal(1)
```

</details>

#### stays silent on array-of-arrays element mutation

- stays silent on array-of-arrays element mutation
- Lint the guaranteed array-of-arrays shape
   - Expected: coll019_count("/tmp/coll019_aoa.spl", AOA_SRC) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("stays silent on array-of-arrays element mutation")
"""`b[0].push(2)` on a [[i64]] mutates in place on every engine and is
a guaranteed idiom under ADR-004 — it must never fire."""
step("Lint the guaranteed array-of-arrays shape")
expect(coll019_count("/tmp/coll019_aoa.spl", AOA_SRC)).to_equal(0)
```

</details>

#### stays silent on the write-back idiom

- stays silent on the write-back idiom
- Lint the ADR-004 conforming write-back form
   - Expected: coll019_count("/tmp/coll019_wb.spl", WRITEBACK_SRC) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("stays silent on the write-back idiom")
step("Lint the ADR-004 conforming write-back form")
expect(coll019_count("/tmp/coll019_wb.spl", WRITEBACK_SRC)).to_equal(0)
```

</details>

#### stays silent on read-only methods through a dict index

- stays silent on read-only methods through a dict index
- Lint a .len() through a dict index
   - Expected: coll019_count("/tmp/coll019_ro.spl", READONLY_SRC) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("stays silent on read-only methods through a dict index")
"""Reading through a copy is fine; only mutation is lost."""
step("Lint a .len() through a dict index")
expect(coll019_count("/tmp/coll019_ro.spl", READONLY_SRC)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/collection_index_mutation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering COLL019 mutation through indexed access.
- COLL019 mutation through indexed access

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `871321b080949fc2e446e243974cb25ed55c5a1a71d9b958d1da4acd708aeffd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `871321b080949fc2e446e243974cb25ed55c5a1a71d9b958d1da4acd708aeffd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `871321b080949fc2e446e243974cb25ed55c5a1a71d9b958d1da4acd708aeffd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/lint/collection_index_mutation_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint/collection_index_mutation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lint/collection_index_mutation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lint/collection_index_mutation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lint/collection_index_mutation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lint/collection_index_mutation_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags a push through a dict-annotated local' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/collection_index_mutation_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags a push through a dict-typed parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/collection_index_mutation_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags a push through a struct field of an indexed element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
