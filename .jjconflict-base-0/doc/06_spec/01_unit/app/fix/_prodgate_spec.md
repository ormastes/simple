# Prodgate Specification

> <details>

<!-- sdn-diagram:id=_prodgate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=_prodgate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

_prodgate_spec -> compiler
_prodgate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=_prodgate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Prodgate Specification

## Scenarios

### prod gate

#### collect_fixes_from_source includes field_access

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "class Box:\n    value: i64\n    me set_value(v: i64):\n        self.value = v\n    me bump():\n        self.set_value(3)\n"
val fixes = collect_fixes_from_source("box.spl", source)
var found = false
for f in fixes:
    if easyfix_id(f).contains("field_access"):
        found = true
expect(found).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `/tmp/wt_work/test/01_unit/app/fix/_prodgate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- prod gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
