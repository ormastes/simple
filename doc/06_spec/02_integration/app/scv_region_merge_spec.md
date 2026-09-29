# scv_region_merge_spec

> Purpose: This spec proves SCV-IMPL-D-05 — semistructured region merge

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_region_merge_spec

Purpose: This spec proves SCV-IMPL-D-05 — semistructured region merge

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_region_merge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV-IMPL-D-05 — semistructured region merge
(MergirafSemi-style). A file is split into CST-region blocks (named
declarations from the P-05 text-block scanner) plus a preamble region; each
region is merged three-way at region granularity, the top-level declaration
list and the preamble `use`-import list are treated as COMMUTATIVE lists
(both sides adding different elements is a clean union, never a conflict),
and every merged result must pass a line-balance check (delimiter balance +
trailing-newline shape) before it is accepted. A region edited differently
on both sides, or delete-vs-edit of the same region, refuses ("" — conflict
stays with the caller); the merge NEVER invents content.
Audience: Maintainers of the SCV merge engine.

## Scenarios

### scv semistructured region merge (D-05)

#### states its version and splits preamble/use regions

**Manual warnings:**
- invalid manual visibility metadata: # @manual SCV commit gates (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-REGION-MERGE-001
# @req REQ-SSPEC-INTEGRATION
expect(scv_region_merge_version()).to_contain("scv/region-merge/v1")
expect(scv_region_preamble(BASE)).to_contain("use std.a")
val uses = scv_region_use_lines(BASE)
expect(uses.len()).to_equal(1)
expect(uses[0]).to_equal("use std.a")
```

</details>

#### merges disjoint region edits and commutative region additions as a clean union

- Left edits alpha and adds gamma; right edits beta and adds delta


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-REGION-MERGE-001
step("Left edits alpha and adds gamma; right edits beta and adds delta")
val left = "use std.a\n\nfn alpha() -> i64:\n    10\n\nfn beta() -> i64:\n    2\n\nfn gamma() -> i64:\n    3\n"
val right = "use std.a\n\nfn alpha() -> i64:\n    1\n\nfn beta() -> i64:\n    20\n\nfn delta() -> i64:\n    4\n"
val merged = scv_region_merge_text(BASE, left, right)
expect(merged).to_contain("    10")
expect(merged).to_contain("    20")
expect(merged).to_contain("fn gamma")
expect(merged).to_contain("fn delta")
val report = scv_region_merge_report(BASE, left, right)
expect(report).to_contain("alpha: left")
expect(report).to_contain("beta: right")
expect(report).to_contain("gamma: left-add")
expect(report).to_contain("delta: right-add")
```

</details>

#### treats the use-import list as commutative: different imports added on each side union cleanly

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-REGION-MERGE-001
val left = "use std.a\nuse std.b\n\nfn alpha() -> i64:\n    1\n\nfn beta() -> i64:\n    2\n"
val right = "use std.a\nuse std.c\n\nfn alpha() -> i64:\n    1\n\nfn beta() -> i64:\n    2\n"
val merged = scv_region_merge_text(BASE, left, right)
expect(merged).to_contain("use std.b")
expect(merged).to_contain("use std.c")
expect(scv_region_merge_report(BASE, left, right)).to_contain("preamble: use-union")
```

</details>

#### refuses when both sides edit the same region differently, and on delete-vs-edit

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-REGION-MERGE-001
val left = "use std.a\n\nfn alpha() -> i64:\n    10\n\nfn beta() -> i64:\n    2\n"
val right = "use std.a\n\nfn alpha() -> i64:\n    99\n\nfn beta() -> i64:\n    2\n"
expect(scv_region_merge_text(BASE, left, right)).to_equal("")
expect(scv_region_merge_report(BASE, left, right)).to_contain("alpha: region-conflict")
# delete-vs-edit: left deletes beta, right edits beta
val dleft = "use std.a\n\nfn alpha() -> i64:\n    1\n"
val dright = "use std.a\n\nfn alpha() -> i64:\n    1\n\nfn beta() -> i64:\n    20\n"
expect(scv_region_merge_text(BASE, dleft, dright)).to_equal("")
expect(scv_region_merge_report(BASE, dleft, dright)).to_contain("beta: delete-edit-conflict")
```

</details>

#### drops a region deleted on one side and unchanged on the other, and line-balance rejects imbalance

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-REGION-MERGE-001
val dleft = "use std.a\n\nfn alpha() -> i64:\n    1\n"
val merged = scv_region_merge_text(BASE, dleft, BASE)
expect(merged).to_contain("fn alpha")
expect(merged.contains("fn beta")).to_equal(false)
expect(scv_region_line_balance_ok("fn a(x: i64) -> i64:\n    f(x)\n")).to_equal(true)
expect(scv_region_line_balance_ok("fn a(x: i64 -> i64:\n    f(x\n")).to_equal(false)
```

</details>

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

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-REGION-MERGE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `705a91b733b776de77479887809db852b9058b72532bfe8c4ce66e26192191e8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `705a91b733b776de77479887809db852b9058b72532bfe8c4ce66e26192191e8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `705a91b733b776de77479887809db852b9058b72532bfe8c4ce66e26192191e8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/02_integration/app/scv_region_merge_spec.spl
mirror: doc/06_spec/02_integration/app/scv_region_merge_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=90
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/scv_region_merge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/scv_region_merge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/scv_region_merge_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/scv_region_merge_spec.spl:32:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'states its version and splits preamble/use regions' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_region_merge_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'merges disjoint region edits and commutative region additions as a clean union' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/scv_region_merge_spec.spl:57:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'treats the use-import list as commutative: different imports added on each side union cleanly' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_region_merge_spec.spl:66:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'refuses when both sides edit the same region differently, and on delete-vs-edit' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_region_merge_spec.spl:78:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'drops a region deleted on one side and unchanged on the other, and line-balance rejects imbalance' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
