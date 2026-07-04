# Tooling Gate Specification

> <details>

<!-- sdn-diagram:id=tooling_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tooling_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tooling_gate_spec -> std
tooling_gate_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tooling_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_tooling_sensitive_path("bin/t32_mcp_server")).to_equal(true)
expect(is_tooling_sensitive_path("src/app/mcp/main.spl")).to_equal(true)
expect(is_tooling_sensitive_path("src/app/lsp/main.spl")).to_equal(true)
expect(is_tooling_sensitive_path(".mcp.json")).to_equal(true)
```

</details>

#### ignores unrelated docs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_tooling_sensitive_path("doc/03_plan/example.md")).to_equal(false)
expect(is_tooling_sensitive_path("src/lib/common/date.spl")).to_equal(false)
```

</details>

### evaluate_evidence_input

#### fails when an artifact is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. make evidence input
2. make evidence input
3. make evidence input
   - Expected: report.status equals `PASS`
   - Expected: report.tooling_paths.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. make evidence input
2. make evidence input
3. make evidence input
   - Expected: report.status equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. make evidence input
2. make evidence input
3. make evidence input
   - Expected: report.status equals `WARN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/verify/tooling_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
