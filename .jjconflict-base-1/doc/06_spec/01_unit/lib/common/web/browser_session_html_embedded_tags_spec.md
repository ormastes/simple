# BrowserSession HTML embedded fallback text projection

> Projects supported embedded-content alternatives and fallback content to

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BrowserSession HTML embedded fallback text projection

Projects supported embedded-content alternatives and fallback content to

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_embedded_tags_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Projects supported embedded-content alternatives and fallback content to
visible text. This is not media loading, layout, or pixel evidence.

## Scenarios

### BrowserSession HTML embedded tag text alternatives

#### should use image alt text inside picture source fallback groups

- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `Hero image`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val html = "<picture><source srcset='hero.avif' type='image/avif'><source srcset='hero.webp' type='image/webp'><img src='hero.png' alt='Hero image'></picture>"
expect(html_to_text(html)).to_equal("Hero image")
```

</details>

#### should use area alt text while preserving embedded fallback text

- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `Area labelFrame fallbackObject fallbackVideo fallbackAudio fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val html = "<map name='m'><area href='/a' alt='Area label'></map><iframe>Frame fallback</iframe><object>Object fallback</object><video><track kind='captions' src='captions.vtt'>Video fallback</video><audio>Audio fallback</audio><embed src='plugin.bin'>"
expect(html_to_text(html)).to_equal("Area labelFrame fallbackObject fallbackVideo fallbackAudio fallback")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
