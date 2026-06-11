# Log Module Export Spec

> Tests that std.log exports are accessible when imported across modules.

<!-- sdn-diagram:id=log_export_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=log_export_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

log_export_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=log_export_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Log Module Export Spec

Tests that std.log exports are accessible when imported across modules.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LOG-EXPORT |
| Category | Stdlib |
| Status | Implemented |
| Source | `test/01_unit/lib/log_export_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests that std.log exports are accessible when imported across modules.
Previously broken: LOG_ERROR (and other constants) were not found when
log functions were called from an importing module.

Root cause was that module-level val/var are not accessible across module
boundaries in the interpreter; fixed by using literal integers in log fns.

## Scenarios

### Log module exports

#### LOG_ERROR constant is accessible

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(LOG_ERROR == 2)
```

</details>

#### LOG_WARN constant is accessible

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(LOG_WARN == 3)
```

</details>

#### LOG_INFO constant is accessible

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(LOG_INFO == 4)
```

</details>

#### LOG_DEBUG constant is accessible

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(LOG_DEBUG == 5)
```

</details>

#### LOG_TRACE constant is accessible

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(LOG_TRACE == 6)
```

</details>

#### LOG_FATAL constant is accessible

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(LOG_FATAL == 1)
```

</details>

#### LOG_OFF constant is accessible

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(LOG_OFF == 0)
```

</details>

#### error function is callable without crash

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### warn function is callable without crash

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
