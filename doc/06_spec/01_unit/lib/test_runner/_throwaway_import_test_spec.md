# _throwaway_import_test_spec

> <details>

<!-- sdn-diagram:id=_throwaway_import_test_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=_throwaway_import_test_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

_throwaway_import_test_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=_throwaway_import_test_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# _throwaway_import_test_spec

Purpose: Import-check probe that also exercises the imported module behaviorally

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/test_runner/_throwaway_import_test_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Import-check probe that also exercises the imported module behaviorally
so a broken export fails here, not silently at load time.
Audience: test-runner engineers who own the imported module.

## Scenarios

### throwaway import check

#### loads classification module

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/test_runner/_throwaway_import_test_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- throwaway import check

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
