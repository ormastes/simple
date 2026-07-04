# Browser Session Storage Specification

> <details>

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
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Storage Specification

## Scenarios

### BrowserSession storage API

#### updates pair lists without changing first-match order

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = Pair(first: "theme", second: "light")
val second = Pair(first: "mode", second: "reader")
val appended = upsert_pair([first], "mode", "reader")
val replaced = upsert_pair(appended, "theme", "dark")

expect(appended.len()).to_equal(2)
expect(appended[0].first).to_equal("theme")
expect(appended[1].first).to_equal("mode")
expect(pair_value(replaced, "theme") ?? "").to_equal("dark")
expect(pair_value(replaced, "mode") ?? "").to_equal("reader")
expect(pair_value(replaced, "missing")).to_be_nil()
```

</details>

#### keeps internal names for storage API property collisions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stored_key = storage_internal_key("getItem")

expect(is_storage_api_property("getItem")).to_equal(true)
expect(storage_public_key_from_internal(stored_key)).to_equal("getItem")
```

</details>

#### keeps storage API methods callable when stored keys use method names

- var session = BrowserSession new
- session open html
- "sessionStorage setItem
- Ok
   - Expected: _display_js(value) equals `function:stored:manual:2`
   - Expected: session.session_storage_item("getItem") ?? "" equals `stored`
   - Expected: session.session_storage_item("length") ?? "" equals `manual`
- Err
- fail
- "sessionStorage removeItem
- Ok
   - Expected: _display_js(value) equals `function:true:1:length`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

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
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
