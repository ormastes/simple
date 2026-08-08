# Html Window Specification

> <details>

<!-- sdn-diagram:id=html_window_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_window_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_window_spec -> std
html_window_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_window_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Window Specification

## Scenarios

### shared HTML window content

#### wraps body HTML with reusable base CSS

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = html_window_content("Demo", html_pre_block("hello"), ".extra{color:red}")

expect(html).to_contain("simple-app-window")
expect(html).to_contain("simple-app-title")
expect(html).to_contain("simple-titlebar-label")
expect(html).to_contain("simple-app-pre")
expect(html).to_contain(".extra{color:red}")
```

</details>

#### bumps the titlebar widget to a 44px touch target on touch devices

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = html_window_content("Demo", html_pre_block("hello"), "")

# Touch-target rule must key on hover:none (the Android emulator and many
# touch devices report pointer:fine), and reach the 44px/48px minimums.
expect(html).to_contain("@media (hover:none),(pointer:coarse)")
expect(html).to_contain("min-height:44px;min-width:44px")
expect(html).to_contain(".simple-app-title{min-height:48px;}")
# Desktop default stays compact.
expect(html).to_contain("min-height:24px")
```

</details>

#### renders title bar widgets with reusable CSS hooks

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val widget = html_titlebar_button("refresh", "Refresh") + html_titlebar_text_input("filter", "ready")
val html = html_window_content_with_titlebar_widgets("Demo", html_pre_block("hello"), widget, ".simple-titlebar-widget{color:lime}")

expect(widget).to_contain("data-simple-titlebar-widget=\"button\"")
expect(widget).to_contain("data-simple-titlebar-widget=\"input\"")
expect(widget).to_contain("data-action=\"refresh\"")
expect(widget).to_contain("data-target-id=\"filter\"")
expect(widget).to_contain("type=\"text\"")
expect(html).to_contain("simple-titlebar-widgets")
expect(html).to_contain("data-action=\"refresh\"")
expect(html).to_contain(".simple-titlebar-input{width:116px;min-width:96px;font-weight:500;cursor:text;}")
expect(html).to_contain(".simple-titlebar-widget{color:lime}")
```

</details>

#### builds picture markup from embedded data URIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uri = html_embedded_image_data_uri("image/png", "abcd")
val pic = html_picture(uri, "Logo")

expect(uri).to_equal("data:image/png;base64,abcd")
expect(pic).to_contain("<picture")
expect(pic).to_contain("src=\"data:image/png;base64,abcd\"")
expect(pic).to_contain("alt=\"Logo\"")
```

</details>

#### escapes text, titles, and picture attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = html_window_content("A < B", html_pre_block("<script>alert(1)</script>"), "")
val pic = html_picture("x\" onerror=\"bad", "A & B")

expect(html).to_contain("A &lt; B")
expect(html).to_contain("&lt;script&gt;alert(1)&lt;/script&gt;")
expect(pic).to_contain("src=\"x&quot; onerror=&quot;bad\"")
expect(pic).to_contain("alt=\"A &amp; B\"")
expect(html_titlebar_button("x\" onclick=\"bad", "A < B")).to_contain("data-action=\"x&quot; onclick=&quot;bad\"")
expect(html_titlebar_button("ok", "A < B")).to_contain("A &lt; B")
expect(html_titlebar_text_input("x\" autofocus bad", "A < B")).to_contain("data-target-id=\"x&quot; autofocus bad\"")
expect(html_titlebar_text_input("ok", "A < B")).to_contain("value=\"A &lt; B\"")
```

</details>

#### exposes CSS blocks for backend-neutral base rendering

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = html_css_block(".demo{color:red}")

expect(block).to_equal("<style>.demo{color:red}</style>")
```

</details>

#### builds WindowInfo using shared HTML content

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = html_window_info("files", "Files", html_picture("file.png", "File"), "", 1, 2, 300, 200)

expect(info.id).to_equal("files")
expect(info.title).to_equal("Files")
expect(info.html).to_contain("simple-picture")
expect(info.x).to_equal(1)
expect(info.width).to_equal(300)
```

</details>

#### builds WindowInfo with title bar widgets

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = html_window_info_with_titlebar_widgets("terminal", "Terminal", html_pre_block("ready"), html_titlebar_button("run", "Run"), "", 4, 5, 320, 240)

expect(info.id).to_equal("terminal")
expect(info.html).to_contain("simple-titlebar-widget")
expect(info.html).to_contain("data-action=\"run\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/html_window_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- shared HTML window content

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
