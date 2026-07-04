# Provider Mime Specification

> <details>

<!-- sdn-diagram:id=provider_mime_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=provider_mime_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

provider_mime_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=provider_mime_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Provider Mime Specification

## Scenarios

### Provider MIME Type Detection

### BaseProvider

#### checks has_key for resource lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = jo1(jp("uri", js("file:///test.spl")))
val has_resource = params.contains("uri")
expect(has_resource).to_equal(true)
```

</details>

#### handles missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = jo1(jp("other", js("value")))
val has_resource = params.contains("uri")
expect(has_resource).to_equal(false)
```

</details>

### FileProvider MIME Detection

#### detects text/plain for .txt files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mime = detect_mime_type("test.txt")
expect(mime).to_equal("text/plain")
```

</details>

#### detects application/json for .json files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mime = detect_mime_type("config.json")
expect(mime).to_equal("application/json")
```

</details>

#### detects text/markdown for .md files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mime = detect_mime_type("README.md")
expect(mime).to_equal("text/markdown")
```

</details>

#### defaults to text/plain for unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mime = detect_mime_type("file.xyz")
expect(mime).to_equal("text/plain")
```

</details>

#### detects text/x-simple for .spl files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mime = detect_mime_type("main.spl")
expect(mime).to_equal("text/x-simple")
```

</details>

### Content Type Categories

#### categorizes PNG as image

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content_type = detect_file_content_type("photo.png")
expect(content_type).to_equal("image")
```

</details>

#### categorizes JPEG as image

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content_type = detect_file_content_type("photo.jpg")
expect(content_type).to_equal("image")
```

</details>

#### categorizes GIF as image

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content_type = detect_file_content_type("anim.gif")
expect(content_type).to_equal("image")
```

</details>

#### categorizes SVG as image

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content_type = detect_file_content_type("icon.svg")
expect(content_type).to_equal("image")
```

</details>

#### categorizes WAV as audio

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content_type = detect_file_content_type("sound.wav")
expect(content_type).to_equal("audio")
```

</details>

#### categorizes MP3 as audio

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content_type = detect_file_content_type("song.mp3")
expect(content_type).to_equal("audio")
```

</details>

#### categorizes SPL as text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content_type = detect_file_content_type("main.spl")
expect(content_type).to_equal("text")
```

</details>

#### defaults unknown to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content_type = detect_file_content_type("data.xyz")
expect(content_type).to_equal("text")
```

</details>

### Image MIME Types

#### PNG maps to image/png

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_mime_type("test.png")).to_equal("image/png")
```

</details>

#### JPEG maps to image/jpeg

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_mime_type("test.jpg")).to_equal("image/jpeg")
```

</details>

#### GIF maps to image/gif

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_mime_type("test.gif")).to_equal("image/gif")
```

</details>

#### SVG maps to image/svg+xml

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_mime_type("test.svg")).to_equal("image/svg+xml")
```

</details>

#### WebP maps to image/webp

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_mime_type("test.webp")).to_equal("image/webp")
```

</details>

### Audio MIME Types

#### WAV maps to audio/wav

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_mime_type("sound.wav")).to_equal("audio/wav")
```

</details>

#### MP3 maps to audio/mpeg

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_mime_type("song.mp3")).to_equal("audio/mpeg")
```

</details>

#### OGG maps to audio/ogg

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_mime_type("clip.ogg")).to_equal("audio/ogg")
```

</details>

### URI Validation

#### validates file:// URIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uri = "file:///home/user/test.spl"
val is_file_uri = uri.starts_with("file://")
expect(is_file_uri).to_equal(true)
```

</details>

#### validates http:// URIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uri = "http://example.com/resource"
val is_http_uri = uri.starts_with("http://")
expect(is_http_uri).to_equal(true)
```

</details>

#### rejects invalid URIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uri = "invalid://test"
val is_valid_file = uri.starts_with("file://")
val is_valid_http = uri.starts_with("http://")
val is_valid = is_valid_file or is_valid_http
expect(is_valid).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/provider_mime_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Provider MIME Type Detection
- BaseProvider
- FileProvider MIME Detection
- Content Type Categories
- Image MIME Types
- Audio MIME Types
- URI Validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
