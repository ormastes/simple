# Browser Session Loading Url Search Params Specification

> <details>

<!-- sdn-diagram:id=browser_session_loading_url_search_params_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_loading_url_search_params_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_loading_url_search_params_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_loading_url_search_params_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Loading Url Search Params Specification

## Scenarios

### BrowserSession loading URLSearchParams helpers

#### decodes plus values and preserves append/set ordering

- query =  url search params set
- query =  url search params append
   - Expected: query equals `q=new+value&empty=&added=more+words`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var query = "q=hello+world&empty=&q=old"

expect(_url_search_params_get(query, "q") ?? "").to_equal("hello world")
expect(_url_search_params_has(query, "empty")).to_be(true)
expect(_url_search_params_has(query, "missing")).to_be(false)

query = _url_search_params_set(query, "q", "new value")
query = _url_search_params_append(query, "added", "more words")

expect(query).to_equal("q=new+value&empty=&added=more+words")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_loading_url_search_params_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession loading URLSearchParams helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
