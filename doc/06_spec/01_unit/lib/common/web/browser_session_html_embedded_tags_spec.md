# Browser Session Html Embedded Tags Specification

> <details>

<!-- sdn-diagram:id=browser_session_html_embedded_tags_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_html_embedded_tags_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_html_embedded_tags_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_html_embedded_tags_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Html Embedded Tags Specification

## Scenarios

### BrowserSession HTML embedded tag text alternatives

#### uses image alt text inside picture source fallback groups

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<picture><source srcset='hero.avif' type='image/avif'><source srcset='hero.webp' type='image/webp'><img src='hero.png' alt='Hero image'></picture>"
expect(html_to_text(html)).to_equal("Hero image")
```

</details>

#### uses area alt text while preserving embedded fallback text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<map name='m'><area href='/a' alt='Area label'></map><iframe>Frame fallback</iframe><object>Object fallback</object><video><track kind='captions' src='captions.vtt'>Video fallback</video><audio>Audio fallback</audio><embed src='plugin.bin'>"
expect(html_to_text(html)).to_equal("Area labelFrame fallbackObject fallbackVideo fallbackAudio fallback")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_embedded_tags_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession HTML embedded tag text alternatives

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
