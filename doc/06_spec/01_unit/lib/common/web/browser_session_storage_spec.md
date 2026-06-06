# Browser Session Storage Specification

> 1. var session = BrowserSession new

<!-- sdn-diagram:id=browser_session_storage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_storage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_storage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_storage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Storage Specification

## Scenarios

### BrowserSession storage API

#### keeps storage API methods callable when stored keys use method names

1. var session = BrowserSession new

2. session open html

3. "sessionStorage setItem

4. Ok
   - Expected: _display_js(value) equals `function:stored:manual:2`
   - Expected: session.session_storage_item("getItem") ?? "" equals `stored`
   - Expected: session.session_storage_item("length") ?? "" equals `manual`

5. Err

6. fail

7. "sessionStorage removeItem

8. Ok
   - Expected: _display_js(value) equals `function:true:1:length`

9. Err

10. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("about:storage-collision", "<html><body>Storage</body></html>")

val set_result = session.eval_script(
    "sessionStorage.setItem('getItem', 'stored'); sessionStorage.setItem('length', 'manual'); typeof sessionStorage.getItem + ':' + sessionStorage.getItem('getItem') + ':' + sessionStorage.getItem('length') + ':' + sessionStorage.length"
)
match set_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("function:stored:manual:2")
        expect(session.session_storage_item("getItem") ?? "").to_equal("stored")
        expect(session.session_storage_item("length") ?? "").to_equal("manual")
    Err(e) =>
        fail("Expected storage collision script to evaluate successfully: {e}")

val remove_result = session.eval_script(
    "sessionStorage.removeItem('getItem'); typeof sessionStorage.getItem + ':' + (sessionStorage.getItem('getItem') === null) + ':' + sessionStorage.length + ':' + sessionStorage.key(0)"
)
match remove_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("function:true:1:length")
        expect(session.session_storage_item("getItem")).to_be_nil()
    Err(e) =>
        fail("Expected storage removeItem script to evaluate successfully: {e}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_storage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession storage API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
