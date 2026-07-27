# Js Async Fetch Specification

> <details>

<!-- sdn-diagram:id=js_async_fetch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=js_async_fetch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

js_async_fetch_spec -> std
js_async_fetch_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=js_async_fetch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Js Async Fetch Specification

## Scenarios

### JS runtime async browser globals

#### installs Promise and fetch globals

- Ok
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = JsRuntime.new(Logger(name: "js-async-test"))
val result = runtime.eval("typeof Promise.resolve + ':' + typeof Promise.prototype.then + ':' + typeof fetch")
match result:
    Ok(value):
        expect(_display_js(value)).to_contain("function:function:function")
    Err(e):
        fail("fetch chain returned Err: {e}")
```

</details>

#### bounds unresolved fetch requests before host dispatch

- The canonical runtime retains at most 1024 unresolved requests.
- Excess `fetch()` calls return an already-rejected Promise without allocating
  a host request record.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/js_async_fetch_spec.spl` |
| Updated | 2026-07-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- JS runtime async browser globals

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
