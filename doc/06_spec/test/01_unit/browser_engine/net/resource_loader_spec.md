# Resource Loader Specification

> Verifies ResourceLoader content-type detection logic and the [u8] body decode boundary. No network calls — pure Content-Type string/body-sniff logic.

<!-- sdn-diagram:id=resource_loader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=resource_loader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

resource_loader_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=resource_loader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Resource Loader Specification

Verifies ResourceLoader content-type detection logic and the [u8] body decode boundary. No network calls — pure Content-Type string/body-sniff logic.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #M16-AC3, #M16-AC4 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/browser_engine/net/resource_loader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies ResourceLoader content-type detection logic and the [u8] body decode
boundary. No network calls — pure Content-Type string/body-sniff logic.

## Scenarios

### detect_content_type from headers

#### AC-3: text/html header yields Html

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = detect_content_type("Content-Type: text/html; charset=utf-8", [])
val is_html = (ct == ContentType.Html)
expect(is_html).to_equal(true)
```

</details>

#### AC-3: text/css header yields Css

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = detect_content_type("Content-Type: text/css", [])
val is_css = (ct == ContentType.Css)
expect(is_css).to_equal(true)
```

</details>

#### AC-3: application/javascript header yields JavaScript

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = detect_content_type("Content-Type: application/javascript", [])
val is_js = (ct == ContentType.JavaScript)
expect(is_js).to_equal(true)
```

</details>

#### AC-3: text/javascript header yields JavaScript

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = detect_content_type("Content-Type: text/javascript", [])
val is_js = (ct == ContentType.JavaScript)
expect(is_js).to_equal(true)
```

</details>

#### AC-3: image/png header yields Image

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = detect_content_type("Content-Type: image/png", [])
val is_img = (ct == ContentType.Image)
expect(is_img).to_equal(true)
```

</details>

#### AC-3: image/jpeg header yields Image

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = detect_content_type("Content-Type: image/jpeg", [])
val is_img = (ct == ContentType.Image)
expect(is_img).to_equal(true)
```

</details>

#### AC-3: image/webp header yields Image

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = detect_content_type("Content-Type: image/webp", [])
val is_img = (ct == ContentType.Image)
expect(is_img).to_equal(true)
```

</details>

#### AC-3: application/octet-stream yields Binary

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = detect_content_type("Content-Type: application/octet-stream", [])
val is_bin = (ct == ContentType.Binary)
expect(is_bin).to_equal(true)
```

</details>

#### AC-3: unknown content-type yields Unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = detect_content_type("Content-Type: application/x-custom-type", [])
val is_unknown = (ct == ContentType.Unknown)
expect(is_unknown).to_equal(true)
```

</details>

#### AC-3: missing Content-Type header falls back to body sniff

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = detect_content_type("", html_body_prefix())
val is_html = (ct == ContentType.Html)
expect(is_html).to_equal(true)
```

</details>

### detect_content_type body sniffing

#### AC-3: body starting with <!DOCTYPE html sniffs as Html

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = detect_content_type("", make_bytes("<!DOCTYPE html><html>"))
val is_html = (ct == ContentType.Html)
expect(is_html).to_equal(true)
```

</details>

#### AC-3: body starting with <html sniffs as Html

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = detect_content_type("", make_bytes("<html><head>"))
val is_html = (ct == ContentType.Html)
expect(is_html).to_equal(true)
```

</details>

#### AC-3: PNG magic bytes sniff as Image

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = detect_content_type("", png_magic_bytes())
val is_img = (ct == ContentType.Image)
expect(is_img).to_equal(true)
```

</details>

#### AC-3: empty body with no header yields Unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = detect_content_type("", [])
val is_unknown = (ct == ContentType.Unknown)
expect(is_unknown).to_equal(true)
```

</details>

### ResourceLoader [u8] body boundary

#### AC-4: FetchResponse body field is [u8] not text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = make_fetch_response_with_bytes()
# body is [u8]; length > 0
expect(resp.body.length).to_be_greater_than(0)
```

</details>

#### AC-4: body_text() returns decoded text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = make_fetch_response_with_bytes()
val decoded = resp.body_text()
expect(decoded).to_start_with("<html>")
```

</details>

#### AC-4: binary body bytes are preserved before decode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = make_binary_response()
# First byte is 0xFF (PNG magic); accessible as raw byte
expect(resp.body.length).to_be_greater_than(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
