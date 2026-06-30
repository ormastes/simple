# Runtime Api Plugin Specification

> <details>

<!-- sdn-diagram:id=runtime_api_plugin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=runtime_api_plugin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

runtime_api_plugin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=runtime_api_plugin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Runtime Api Plugin Specification

## Scenarios

### Runtime API plugin - AC-1

#### fixture .so exists (run build_fixtures.shs first)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists(fixture_library())).to_equal(true)
```

</details>

#### use_plugin loads the demo entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = use_plugin_from(fixture_manifest(), "demo")
expect(ok).to_equal(true)
```

</details>

#### list_plugins reports demo by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _ok = use_plugin_from(fixture_manifest(), "demo")
val names = list_plugins()
var found = false
for n in names:
    if n == "demo":
        found = true
expect(found).to_equal(true)
```

</details>

#### plugin_call_i64 dispatches simple_demo_add(4, 5) = 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _ok = use_plugin_from(fixture_manifest(), "demo")
val result = plugin_call_i64("simple_demo_add", [4, 5])
expect(result).to_equal(9)
```

</details>

#### plugin_call_i64 returns consistent results across edge values

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _ok = use_plugin_from(fixture_manifest(), "demo")
val r1 = plugin_call_i64("simple_demo_add", [0, 0])
val r2 = plugin_call_i64("simple_demo_add", [-1, 1])
val r3 = plugin_call_i64("simple_demo_add", [1000000, 1000000])
expect(r1).to_equal(0)
expect(r2).to_equal(0)
expect(r3).to_equal(2000000)
```

</details>

#### plugin_call_f64 dispatches simple_demo_add_scaled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _ok = use_plugin_from(fixture_manifest(), "demo")
val result = plugin_call_f64("simple_demo_add_scaled", [1.25, 2.75, 0.5])
expect(result).to_equal(2.0)
```

</details>

#### use_plugin_from returns false for unknown name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = use_plugin_from(fixture_manifest(), "nonexistent")
expect(ok).to_equal(false)
```

</details>

#### WFFI f64 surface covers scalar plugin calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FR-PLUG-0001 resolves the old i64-only carve-out by exposing
# spl_wffi_call_f64 and std.plugin.plugin_call_f64.
expect(plugin_call_f64("simple_demo_add_scaled", [1.0, 2.0, 3.0])).to_equal(9.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/plugin/runtime_api_plugin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Runtime API plugin - AC-1

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
