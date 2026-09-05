# Tooling Gate Specification

> Tests covering app.verify.tooling_gate, is_tooling_sensitive_path, evaluate_evidence_input, build_tooling_verify_report.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tooling Gate Specification

## Scenarios

### app.verify.tooling_gate

### is_tooling_sensitive_path

#### matches wrapper and mcp paths

- matches wrapper and mcp paths
   - Expected: is_tooling_sensitive_path("bin/t32_mcp_server") is true
   - Expected: is_tooling_sensitive_path("src/app/mcp/main.spl") is true
   - Expected: is_tooling_sensitive_path("src/app/lsp/main.spl") is true
   - Expected: is_tooling_sensitive_path(".mcp.json") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches wrapper and mcp paths")
expect(is_tooling_sensitive_path("bin/t32_mcp_server")).to_equal(true)
expect(is_tooling_sensitive_path("src/app/mcp/main.spl")).to_equal(true)
expect(is_tooling_sensitive_path("src/app/lsp/main.spl")).to_equal(true)
expect(is_tooling_sensitive_path(".mcp.json")).to_equal(true)
```

</details>

#### ignores unrelated docs

- ignores unrelated docs
   - Expected: is_tooling_sensitive_path("doc/03_plan/example.md") is false
   - Expected: is_tooling_sensitive_path("src/lib/common/date.spl") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores unrelated docs")
expect(is_tooling_sensitive_path("doc/03_plan/example.md")).to_equal(false)
expect(is_tooling_sensitive_path("src/lib/common/date.spl")).to_equal(false)
```

</details>

### evaluate_evidence_input

#### fails when an artifact is missing

- fails when an artifact is missing
   - Expected: finding.level equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when an artifact is missing")
val finding = evaluate_evidence_input(make_evidence_input(
    "Wrapper audit",
    "doc/09_report/verify/mcp_wrapper_audit.md",
    false,
    "",
    []
))
expect(finding.level).to_equal("FAIL")
expect(finding.message).to_contain("missing")
```

</details>

#### fails when performance evidence misses required tokens

- fails when performance evidence misses required tokens
   - Expected: finding.level equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when performance evidence misses required tokens")
val finding = evaluate_evidence_input(make_evidence_input(
    "Performance evidence",
    "doc/09_report/verify/mcp_perf_evidence.md",
    true,
    "STATUS: PASS\nwarm startup: 0.02s\n",
    ["warm startup", "representative request", "max rss"]
))
expect(finding.level).to_equal("FAIL")
expect(finding.message).to_contain("representative request")
expect(finding.message).to_contain("max rss")
```

</details>

#### warns when an artifact reports warn

- warns when an artifact reports warn
   - Expected: finding.level equals `WARN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns when an artifact reports warn")
val finding = evaluate_evidence_input(make_evidence_input(
    "Request-path audit",
    "doc/09_report/verify/mcp_request_path_audit.md",
    true,
    "STATUS: WARN\none hot path still shells out\n",
    []
))
expect(finding.level).to_equal("WARN")
```

</details>

### build_tooling_verify_report

#### skips the tooling gate for non-tooling changes

- skips the tooling gate for non-tooling changes
   - Expected: report.status equals `PASS`
   - Expected: report.tooling_paths.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips the tooling gate for non-tooling changes")
val report = build_tooling_verify_report(
    "current changes",
    ["doc/03_plan/example.md", "README.md"],
    make_evidence_input("Wrapper audit", "wrapper", false, "", []),
    make_evidence_input("Request-path audit", "request", false, "", []),
    make_evidence_input("Performance evidence", "perf", false, "", ["warm startup"])
)
expect(report.status).to_equal("PASS")
expect(report.tooling_paths.len()).to_equal(0)
val rendered = render_verify_report(report)
expect(rendered).to_contain("tooling gate skipped")
```

</details>

#### fails when tooling changes are present and evidence is missing

- fails when tooling changes are present and evidence is missing
   - Expected: report.status equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when tooling changes are present and evidence is missing")
val report = build_tooling_verify_report(
    "current changes",
    ["src/app/mcp/main.spl", "src/app/verify/main.spl"],
    make_evidence_input("Wrapper audit", "wrapper", false, "", []),
    make_evidence_input("Request-path audit", "request", true, "STATUS: PASS\n", []),
    make_evidence_input("Performance evidence", "perf", true, "STATUS: PASS\nwarm startup\nrepresentative request\nmax rss\n", ["warm startup", "representative request", "max rss"])
)
expect(report.status).to_equal("FAIL")
expect(report.failures).to_be_greater_than(0)
val rendered = render_verify_report(report)
expect(rendered).to_contain("[FAIL] wrapper")
expect(rendered).to_contain("STATUS: FAIL")
```

</details>

#### returns warn when evidence reports warn without failures

- returns warn when evidence reports warn without failures
   - Expected: report.status equals `WARN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns warn when evidence reports warn without failures")
val report = build_tooling_verify_report(
    "current changes",
    ["bin/simple_mcp_server"],
    make_evidence_input("Wrapper audit", "wrapper", true, "STATUS: PASS\n", []),
    make_evidence_input("Request-path audit", "request", true, "STATUS: WARN\nlegacy hot path remains\n", []),
    make_evidence_input("Performance evidence", "perf", true, "STATUS: PASS\nwarm startup\nrepresentative request\nmax rss\n", ["warm startup", "representative request", "max rss"])
)
expect(report.status).to_equal("WARN")
val rendered = render_verify_report(report)
expect(rendered).to_contain("[WARN] request")
expect(rendered).to_contain("STATUS: WARN")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/verify/tooling_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering app.verify.tooling_gate, is_tooling_sensitive_path, evaluate_evidence_input, build_tooling_verify_report.
- app.verify.tooling_gate
- is_tooling_sensitive_path
- evaluate_evidence_input
- build_tooling_verify_report

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `46a3eee579cb2045bd76f126404e42bdfdc8ad69c2a1b8fdafc8f525e3c2e4d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `46a3eee579cb2045bd76f126404e42bdfdc8ad69c2a1b8fdafc8f525e3c2e4d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `46a3eee579cb2045bd76f126404e42bdfdc8ad69c2a1b8fdafc8f525e3c2e4d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/verify/tooling_gate_spec.spl
mirror: doc/06_spec/unit/app/verify/tooling_gate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/verify/tooling_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/verify/tooling_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/verify/tooling_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/verify/tooling_gate_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches wrapper and mcp paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/verify/tooling_gate_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ignores unrelated docs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/verify/tooling_gate_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails when an artifact is missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
