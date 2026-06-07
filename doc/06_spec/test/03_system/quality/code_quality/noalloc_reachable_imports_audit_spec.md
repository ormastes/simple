# Noalloc Reachable Imports Audit Specification

> <details>

<!-- sdn-diagram:id=noalloc_reachable_imports_audit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=noalloc_reachable_imports_audit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

noalloc_reachable_imports_audit_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=noalloc_reachable_imports_audit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Noalloc Reachable Imports Audit Specification

## Scenarios

### noalloc reachable imports audit

#### keeps reachable noalloc imports restricted to noalloc and common roots

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_process_run("bin/simple", ["run", "scripts/audit/noalloc_reachable_imports.spl"])
expect(result.2).to_equal(0)
expect(result.0).to_contain("noalloc reachable import closure is restricted to nogc_async_mut_noalloc/common")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/code_quality/noalloc_reachable_imports_audit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- noalloc reachable imports audit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
