# Resource Loader Specification

> Verifies ResourceLoader content-type detection logic and the [u8] body decode boundary. No network calls — pure Content-Type string/body-sniff logic.

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
| Source | `test/unit/browser_engine/net/resource_loader_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies ResourceLoader content-type detection logic and the [u8] body decode
boundary. No network calls — pure Content-Type string/body-sniff logic.

## Scenarios

### detect_content_type from headers

#### AC-3: text/html header yields Html

- AC-3: text/html header yields Html
   - Expected: is_html is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: text/html header yields Html")
val ct = detect_content_type("Content-Type: text/html; charset=utf-8", [])
val is_html = (ct == ContentType.Html)
expect(is_html).to_equal(true)
```

</details>

#### AC-3: text/css header yields Css

- AC-3: text/css header yields Css
   - Expected: is_css is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: text/css header yields Css")
val ct = detect_content_type("Content-Type: text/css", [])
val is_css = (ct == ContentType.Css)
expect(is_css).to_equal(true)
```

</details>

#### AC-3: application/javascript header yields JavaScript

- AC-3: application/javascript header yields JavaScript
   - Expected: is_js is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: application/javascript header yields JavaScript")
val ct = detect_content_type("Content-Type: application/javascript", [])
val is_js = (ct == ContentType.JavaScript)
expect(is_js).to_equal(true)
```

</details>

#### AC-3: text/javascript header yields JavaScript

- AC-3: text/javascript header yields JavaScript
   - Expected: is_js is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: text/javascript header yields JavaScript")
val ct = detect_content_type("Content-Type: text/javascript", [])
val is_js = (ct == ContentType.JavaScript)
expect(is_js).to_equal(true)
```

</details>

#### AC-3: image/png header yields Image

- AC-3: image/png header yields Image
   - Expected: is_img is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: image/png header yields Image")
val ct = detect_content_type("Content-Type: image/png", [])
val is_img = (ct == ContentType.Image)
expect(is_img).to_equal(true)
```

</details>

#### AC-3: image/jpeg header yields Image

- AC-3: image/jpeg header yields Image
   - Expected: is_img is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: image/jpeg header yields Image")
val ct = detect_content_type("Content-Type: image/jpeg", [])
val is_img = (ct == ContentType.Image)
expect(is_img).to_equal(true)
```

</details>

#### AC-3: image/webp header yields Image

- AC-3: image/webp header yields Image
   - Expected: is_img is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: image/webp header yields Image")
val ct = detect_content_type("Content-Type: image/webp", [])
val is_img = (ct == ContentType.Image)
expect(is_img).to_equal(true)
```

</details>

#### AC-3: application/octet-stream yields Binary

- AC-3: application/octet-stream yields Binary
   - Expected: is_bin is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: application/octet-stream yields Binary")
val ct = detect_content_type("Content-Type: application/octet-stream", [])
val is_bin = (ct == ContentType.Binary)
expect(is_bin).to_equal(true)
```

</details>

#### AC-3: unknown content-type yields Unknown

- AC-3: unknown content-type yields Unknown
   - Expected: is_unknown is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: unknown content-type yields Unknown")
val ct = detect_content_type("Content-Type: application/x-custom-type", [])
val is_unknown = (ct == ContentType.Unknown)
expect(is_unknown).to_equal(true)
```

</details>

#### AC-3: missing Content-Type header falls back to body sniff

- AC-3: missing Content-Type header falls back to body sniff
   - Expected: is_html is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: missing Content-Type header falls back to body sniff")
val ct = detect_content_type("", html_body_prefix())
val is_html = (ct == ContentType.Html)
expect(is_html).to_equal(true)
```

</details>

### detect_content_type body sniffing

#### AC-3: body starting with <!DOCTYPE html sniffs as Html

- AC-3: body starting with <!DOCTYPE html sniffs as Html
   - Expected: is_html is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: body starting with <!DOCTYPE html sniffs as Html")
val ct = detect_content_type("", make_bytes("<!DOCTYPE html><html>"))
val is_html = (ct == ContentType.Html)
expect(is_html).to_equal(true)
```

</details>

#### AC-3: body starting with <html sniffs as Html

- AC-3: body starting with <html sniffs as Html
   - Expected: is_html is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: body starting with <html sniffs as Html")
val ct = detect_content_type("", make_bytes("<html><head>"))
val is_html = (ct == ContentType.Html)
expect(is_html).to_equal(true)
```

</details>

#### AC-3: PNG magic bytes sniff as Image

- AC-3: PNG magic bytes sniff as Image
   - Expected: is_img is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: PNG magic bytes sniff as Image")
val ct = detect_content_type("", png_magic_bytes())
val is_img = (ct == ContentType.Image)
expect(is_img).to_equal(true)
```

</details>

#### AC-3: empty body with no header yields Unknown

- AC-3: empty body with no header yields Unknown
   - Expected: is_unknown is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: empty body with no header yields Unknown")
val ct = detect_content_type("", [])
val is_unknown = (ct == ContentType.Unknown)
expect(is_unknown).to_equal(true)
```

</details>

### ResourceLoader [u8] body boundary

#### AC-4: FetchResponse body field is [u8] not text

- AC-4: FetchResponse body field is [u8] not text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: FetchResponse body field is [u8] not text")
val resp = make_fetch_response_with_bytes()
# body is [u8]; length > 0
expect(resp.body.length).to_be_greater_than(0)
```

</details>

#### AC-4: body_text() returns decoded text

- AC-4: body_text() returns decoded text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: body_text() returns decoded text")
val resp = make_fetch_response_with_bytes()
val decoded = resp.body_text()
expect(decoded).to_start_with("<html>")
```

</details>

#### AC-4: binary body bytes are preserved before decode

- AC-4: binary body bytes are preserved before decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: binary body bytes are preserved before decode")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `feda2b45e32324ea007a02f9f02ab649669ec6974e3b169cc2bae2b56d42c470`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `feda2b45e32324ea007a02f9f02ab649669ec6974e3b169cc2bae2b56d42c470`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `feda2b45e32324ea007a02f9f02ab649669ec6974e3b169cc2bae2b56d42c470`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/browser_engine/net/resource_loader_spec.spl
mirror: doc/06_spec/unit/browser_engine/net/resource_loader_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/browser_engine/net/resource_loader_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/browser_engine/net/resource_loader_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/browser_engine/net/resource_loader_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: text/html header yields Html' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser_engine/net/resource_loader_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: text/css header yields Css' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser_engine/net/resource_loader_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: application/javascript header yields JavaScript' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
