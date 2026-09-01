# Provider Mime Specification

> Tests covering Provider MIME Type Detection, BaseProvider, FileProvider MIME Detection, Content Type Categories, Image MIME Types, Audio MIME Types, URI Validation.

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

- checks has_key for resource lookup
   - Expected: has_resource is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks has_key for resource lookup")
val params = jo1(jp("uri", js("file:///test.spl")))
val has_resource = params.contains("uri")
expect(has_resource).to_equal(true)
```

</details>

#### handles missing key

- handles missing key
   - Expected: has_resource is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles missing key")
val params = jo1(jp("other", js("value")))
val has_resource = params.contains("uri")
expect(has_resource).to_equal(false)
```

</details>

### FileProvider MIME Detection

#### detects text/plain for .txt files

- detects text/plain for .txt files
   - Expected: mime equals `text/plain`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects text/plain for .txt files")
val mime = detect_mime_type("test.txt")
expect(mime).to_equal("text/plain")
```

</details>

#### detects application/json for .json files

- detects application/json for .json files
   - Expected: mime equals `application/json`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects application/json for .json files")
val mime = detect_mime_type("config.json")
expect(mime).to_equal("application/json")
```

</details>

#### detects text/markdown for .md files

- detects text/markdown for .md files
   - Expected: mime equals `text/markdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects text/markdown for .md files")
val mime = detect_mime_type("README.md")
expect(mime).to_equal("text/markdown")
```

</details>

#### defaults to text/plain for unknown

- defaults to text/plain for unknown
   - Expected: mime equals `text/plain`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to text/plain for unknown")
val mime = detect_mime_type("file.xyz")
expect(mime).to_equal("text/plain")
```

</details>

#### detects text/x-simple for .spl files

- detects text/x-simple for .spl files
   - Expected: mime equals `text/x-simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects text/x-simple for .spl files")
val mime = detect_mime_type("main.spl")
expect(mime).to_equal("text/x-simple")
```

</details>

### Content Type Categories

#### categorizes PNG as image

- categorizes PNG as image
   - Expected: content_type equals `image`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes PNG as image")
val content_type = detect_file_content_type("photo.png")
expect(content_type).to_equal("image")
```

</details>

#### categorizes JPEG as image

- categorizes JPEG as image
   - Expected: content_type equals `image`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes JPEG as image")
val content_type = detect_file_content_type("photo.jpg")
expect(content_type).to_equal("image")
```

</details>

#### categorizes GIF as image

- categorizes GIF as image
   - Expected: content_type equals `image`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes GIF as image")
val content_type = detect_file_content_type("anim.gif")
expect(content_type).to_equal("image")
```

</details>

#### categorizes SVG as image

- categorizes SVG as image
   - Expected: content_type equals `image`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes SVG as image")
val content_type = detect_file_content_type("icon.svg")
expect(content_type).to_equal("image")
```

</details>

#### categorizes WAV as audio

- categorizes WAV as audio
   - Expected: content_type equals `audio`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes WAV as audio")
val content_type = detect_file_content_type("sound.wav")
expect(content_type).to_equal("audio")
```

</details>

#### categorizes MP3 as audio

- categorizes MP3 as audio
   - Expected: content_type equals `audio`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes MP3 as audio")
val content_type = detect_file_content_type("song.mp3")
expect(content_type).to_equal("audio")
```

</details>

#### categorizes SPL as text

- categorizes SPL as text
   - Expected: content_type equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes SPL as text")
val content_type = detect_file_content_type("main.spl")
expect(content_type).to_equal("text")
```

</details>

#### defaults unknown to text

- defaults unknown to text
   - Expected: content_type equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults unknown to text")
val content_type = detect_file_content_type("data.xyz")
expect(content_type).to_equal("text")
```

</details>

### Image MIME Types

#### PNG maps to image/png

- PNG maps to image/png
   - Expected: detect_mime_type("test.png") equals `image/png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PNG maps to image/png")
expect(detect_mime_type("test.png")).to_equal("image/png")
```

</details>

#### JPEG maps to image/jpeg

- JPEG maps to image/jpeg
   - Expected: detect_mime_type("test.jpg") equals `image/jpeg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("JPEG maps to image/jpeg")
expect(detect_mime_type("test.jpg")).to_equal("image/jpeg")
```

</details>

#### GIF maps to image/gif

- GIF maps to image/gif
   - Expected: detect_mime_type("test.gif") equals `image/gif`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GIF maps to image/gif")
expect(detect_mime_type("test.gif")).to_equal("image/gif")
```

</details>

#### SVG maps to image/svg+xml

- SVG maps to image/svg+xml
   - Expected: detect_mime_type("test.svg") equals `image/svg+xml`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SVG maps to image/svg+xml")
expect(detect_mime_type("test.svg")).to_equal("image/svg+xml")
```

</details>

#### WebP maps to image/webp

- WebP maps to image/webp
   - Expected: detect_mime_type("test.webp") equals `image/webp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("WebP maps to image/webp")
expect(detect_mime_type("test.webp")).to_equal("image/webp")
```

</details>

### Audio MIME Types

#### WAV maps to audio/wav

- WAV maps to audio/wav
   - Expected: detect_mime_type("sound.wav") equals `audio/wav`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("WAV maps to audio/wav")
expect(detect_mime_type("sound.wav")).to_equal("audio/wav")
```

</details>

#### MP3 maps to audio/mpeg

- MP3 maps to audio/mpeg
   - Expected: detect_mime_type("song.mp3") equals `audio/mpeg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MP3 maps to audio/mpeg")
expect(detect_mime_type("song.mp3")).to_equal("audio/mpeg")
```

</details>

#### OGG maps to audio/ogg

- OGG maps to audio/ogg
   - Expected: detect_mime_type("clip.ogg") equals `audio/ogg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("OGG maps to audio/ogg")
expect(detect_mime_type("clip.ogg")).to_equal("audio/ogg")
```

</details>

### URI Validation

#### validates file:// URIs

- validates file:// URIs
   - Expected: is_file_uri is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates file:// URIs")
val uri = "file:///home/user/test.spl"
val is_file_uri = uri.starts_with("file://")
expect(is_file_uri).to_equal(true)
```

</details>

#### validates http:// URIs

- validates http:// URIs
   - Expected: is_http_uri is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates http:// URIs")
val uri = "http://example.com/resource"
val is_http_uri = uri.starts_with("http://")
expect(is_http_uri).to_equal(true)
```

</details>

#### rejects invalid URIs

- rejects invalid URIs
   - Expected: is_valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid URIs")
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
| Source | `test/unit/app/mcp_unit/provider_mime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Provider MIME Type Detection, BaseProvider, FileProvider MIME Detection, Content Type Categories, Image MIME Types, Audio MIME Types, URI Validation.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `79774b5c2ce8bd95d77791577603be9179b285dfe7ac868794372b51985184c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `79774b5c2ce8bd95d77791577603be9179b285dfe7ac868794372b51985184c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `79774b5c2ce8bd95d77791577603be9179b285dfe7ac868794372b51985184c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/provider_mime_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/provider_mime_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/provider_mime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/provider_mime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/provider_mime_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks has_key for resource lookup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/provider_mime_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles missing key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/provider_mime_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects text/plain for .txt files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
