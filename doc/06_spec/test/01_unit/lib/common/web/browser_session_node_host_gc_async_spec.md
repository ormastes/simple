# Browser Session Node Host Gc Async Specification

> 1. var interp = gc js JsInterpreter new

<!-- sdn-diagram:id=browser_session_node_host_gc_async_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_node_host_gc_async_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_node_host_gc_async_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_node_host_gc_async_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Node Host Gc Async Specification

## Scenarios

### BrowserSession gc_async Node host require cache

#### reuses builtin module objects across node-prefixed aliases

1. var interp = gc js JsInterpreter new
2. JsValue Object
3. interp set object property
   - Expected: "missing path module" equals `object`
   - Expected: _object_property_text(interp, interp._native_node_require([JsValue.String(v: "node:path")]), "cacheProbe") equals `yes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = gc_js.JsInterpreter.new(Logger.new(LogLevel.Error))

val path = interp._native_node_require([JsValue.String(v: "path")])
match path:
    JsValue.Object(path_id):
        interp.set_object_property(path_id, "cacheProbe", JsValue.String(v: "yes"))
    _:
        expect("missing path module").to_equal("object")

expect(_object_property_text(interp, interp._native_node_require([JsValue.String(v: "node:path")]), "cacheProbe")).to_equal("yes")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_node_host_gc_async_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession gc_async Node host require cache

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
