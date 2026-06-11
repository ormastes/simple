# Navigation Fetch Specification

> Tests for `fetch_text` (file:// reads, invalid URL rejection, unsupported scheme rejection) and for the new `NavigationController.goto` method that fetches a URL before recording it in history.

<!-- sdn-diagram:id=navigation_fetch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=navigation_fetch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

navigation_fetch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=navigation_fetch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Navigation Fetch Specification

Tests for `fetch_text` (file:// reads, invalid URL rejection, unsupported scheme rejection) and for the new `NavigationController.goto` method that fetches a URL before recording it in history.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/01_unit/lib/blink/navigation_fetch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `fetch_text` (file:// reads, invalid URL rejection, unsupported
scheme rejection) and for the new `NavigationController.goto` method that
fetches a URL before recording it in history.

Real network traffic is out of scope — http:// URLs are not exercised here
because they would break CI. The file:// path is smoke-tested via a temp
file written and deleted inside each `it` block.

## Scenarios

### fetch_text file://

#### reads a local file and returns body

1. rt file write text
2. rt file delete
   - Expected: result.is_ok() is true
   - Expected: resp.status equals `200`
   - Expected: resp.body equals `html`
   - Expected: resp.content_type equals `text/html`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/blink_fetch_smoke.html"
val html = "<html><body>hello</body></html>"
rt_file_write_text(path, html)
val result = fetch_text("file://{path}")
rt_file_delete(path)
expect(result.is_ok()).to_equal(true)
val resp = result.unwrap()
expect(resp.status).to_equal(200)
expect(resp.body).to_equal(html)
expect(resp.content_type).to_equal("text/html")
```

</details>

#### returns Err for a missing file

1. rt file delete
   - Expected: result.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/blink_fetch_missing_xyz.html"
# Ensure the file does not exist.
rt_file_delete(path)
val result = fetch_text("file://{path}")
expect(result.is_ok()).to_equal(false)
```

</details>

### fetch_text invalid inputs

#### returns Err for a non-URL string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = fetch_text("not a url")
expect(result.is_ok()).to_equal(false)
```

</details>

#### returns Err with a meaningful message for an unsupported scheme

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = fetch_text("ftp://unsupported")
expect(result.is_ok()).to_equal(false)
if val Err(msg) = result:
    expect(msg).to_contain("unsupported scheme")
```

</details>

### NavigationController.goto

#### updates the controller's current entry on file:// fetch

1. rt file write text
2. rt file delete
   - Expected: result.is_ok() is true
   - Expected: nc.history_count() equals `1`
   - Expected: nc.current_index equals `0`
   - Expected: cur is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/blink_fetch_smoke.html"
rt_file_write_text(path, "<html></html>")
val nc = navigation_controller_new()
val url = "file://{path}"
val result = nc.goto(url, 1000.0)
rt_file_delete(path)
expect(result.is_ok()).to_equal(true)
expect(nc.history_count()).to_equal(1)
expect(nc.current_index).to_equal(0)
val cur = nc.current_entry()
expect(cur).to_equal(false)  # not nil — history advanced
```

</details>

#### leaves history unchanged on invalid URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nc = navigation_controller_new()
val result = nc.goto("", 1000.0)
expect(result.is_ok()).to_equal(false)
expect(nc.history_count()).to_equal(0)
expect(nc.current_index).to_equal(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
