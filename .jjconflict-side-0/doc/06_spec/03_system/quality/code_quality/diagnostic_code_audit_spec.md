# Diagnostic Code Audit Specification

> <details>

<!-- sdn-diagram:id=diagnostic_code_audit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=diagnostic_code_audit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

diagnostic_code_audit_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=diagnostic_code_audit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diagnostic Code Audit Specification

## Scenarios

### diagnostic code audit

#### accepts current compiler app and Rust CLI diagnostic code literals

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_process_run("bin/simple", ["run", "scripts/audit/diagnostic_code_audit.spl"])
expect(result.2).to_equal(0)
expect(result.0).to_contain("Diagnostic Code Audit")
expect(result.0).to_contain("All diagnostic code literals use stable public shapes")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/code_quality/diagnostic_code_audit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- diagnostic code audit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
