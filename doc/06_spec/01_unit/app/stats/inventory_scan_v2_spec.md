# Inventory Scan V2 Specification

> Tests covering stats inventory scanner v2.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inventory Scan V2 Specification

## Scenarios

### stats inventory scanner v2

#### counts code without blanks and language comments

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- counts code without blanks and language comments
   - Expected: stats_count_sloc("src/demo.spl", "# note\nfn main():\n    1\n\n") equals `2`
   - Expected: stats_count_sloc("src/demo.c", "// note\n/* block\nend */\nint x;\n") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("counts code without blanks and language comments")
expect(stats_count_sloc("src/demo.spl", "# note\nfn main():\n    1\n\n")).to_equal(2)
expect(stats_count_sloc("src/demo.c", "// note\n/* block\nend */\nint x;\n")).to_equal(1)
```

</details>

#### counts Markdown fenced and source comment tests

- counts Markdown fenced and source comment tests
   - Expected: stats_markdown_test_sloc(md) equals `2`
   - Expected: stats_comment_test_sloc("# >>> 1 + 1\n>>> 2 + 2\n") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("counts Markdown fenced and source comment tests")
val md = "text\n```simple\nval x = 1\nexpect(x).to_equal(1)\n```\n"
expect(stats_markdown_test_sloc(md)).to_equal(2)
expect(stats_comment_test_sloc("# >>> 1 + 1\n>>> 2 + 2\n")).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/stats/inventory_scan_v2_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering stats inventory scanner v2.
- stats inventory scanner v2

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c77c630403fa3675dec55c1ac6ee2f8d269a3904de094643f2d325fe06d7a970`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c77c630403fa3675dec55c1ac6ee2f8d269a3904de094643f2d325fe06d7a970`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c77c630403fa3675dec55c1ac6ee2f8d269a3904de094643f2d325fe06d7a970`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/stats/inventory_scan_v2_spec.spl
mirror: doc/06_spec/01_unit/app/stats/inventory_scan_v2_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/stats/inventory_scan_v2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/stats/inventory_scan_v2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/stats/inventory_scan_v2_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/stats/inventory_scan_v2_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts code without blanks and language comments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/stats/inventory_scan_v2_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts Markdown fenced and source comment tests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
