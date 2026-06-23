# Semver Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=semver_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=semver_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

semver_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=semver_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Semver Numeric Guard Specification

## Scenarios

### package semver numeric guard

#### rejects malformed numeric components without direct parse crashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nogc_sync = rt_file_read_text("src/lib/nogc_sync_mut/package/semver.spl") ?? ""
val nogc_async = rt_file_read_text("src/lib/nogc_async_mut/package/semver.spl") ?? ""
val gc_async = rt_file_read_text("src/lib/gc_async_mut/package/semver.spl") ?? ""
val nogc_sync_old = rt_file_read_text("src/lib/nogc_sync_mut/package/semver_old.spl") ?? ""
val nogc_async_old = rt_file_read_text("src/lib/nogc_async_mut/package/semver_old.spl") ?? ""
val gc_async_old = rt_file_read_text("src/lib/gc_async_mut/package/semver_old.spl") ?? ""

expect(nogc_sync).to_contain("if ch < \"0\" or ch > \"9\":")
expect(nogc_async).to_contain("if ch < \"0\" or ch > \"9\":")
expect(gc_async).to_contain("if ch < \"0\" or ch > \"9\":")
expect(nogc_sync_old).to_contain("if ch < \"0\" or ch > \"9\":")
expect(nogc_async_old).to_contain("if ch < \"0\" or ch > \"9\":")
expect(gc_async_old).to_contain("if ch < \"0\" or ch > \"9\":")
expect(nogc_sync).to_contain("if num == nil:")
expect(nogc_async).to_contain("if num == nil:")
expect(gc_async).to_contain("if num == nil:")
expect(nogc_sync_old).to_contain("if num == nil:")
expect(nogc_async_old).to_contain("if num == nil:")
expect(gc_async_old).to_contain("if num == nil:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/package/semver_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- package semver numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
