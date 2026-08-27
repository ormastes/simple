# Web rendering: CSS essentials used by the standards showcase

> Renders a compact page exercising the exact CSS features the showcase page

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web rendering: CSS essentials used by the standards showcase

Renders a compact page exercising the exact CSS features the showcase page

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_web/feature/web_css_essentials_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Renders a compact page exercising the exact CSS features the showcase page
(`examples/06_io/ui/browser_common_elements_showcase.html`) depends on —
element/id/class selectors, `background`, `color`, `padding`, `margin`,
`border: 0` — through the pure-Simple web renderer on the deterministic
cpu_simd engine2d lane, and asserts EXACT pixel anchors:

- `header { background: #173b7a }` — header band
- `body { background: #eef2ff }` — page ground
- `.card { background: white }` — class selector + white card
- `button { background: #4f46e5 }` — button fill
- `<mark>` — yellow highlight
- `a { color: #1d4ed8 }` — anchor text renders blue-dominant pixels

Anchors were measured from a reference render of the same page; exact-color
assertions are derived from the CSS values (no fitted tolerances), and the
anchor-text check tolerates antialiasing by testing blue dominance, not
equality.

## Scenarios

### Web CSS essentials — showcase feature set

#### renders header, body ground, card, button, mark, and anchor colors exactly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders header, body ground, card, button, mark, and anchor colors exactly
- Render the essentials page on the cpu_simd lane
   - Expected: pixels.len() equals `W * H`
- Header band is exactly #173b7a
   - Expected: pixel_at(pixels, 200, 10) equals `0xFF173B7Au32`
- Body ground is exactly #eef2ff
   - Expected: pixel_at(pixels, 380, 295) equals `0xFFEEF2FFu32`
- Card background is white (class selector applied)
   - Expected: pixel_at(pixels, 200, 90) equals `0xFFFFFFFFu32`
- Button fill is exactly #4f46e5
   - Expected: pixel_at(pixels, 40, 133) equals `0xFF4F46E5u32`
- Mark highlight is exactly yellow
   - Expected: pixel_at(pixels, 117, 103) equals `0xFFFFFF00u32`
- Anchor text carries blue-dominant pixels
   - Expected: has_blue_dominant_pixel(pixels, 60, 95, 120, 112) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders header, body ground, card, button, mark, and anchor colors exactly")
step("Render the essentials page on the cpu_simd lane")
val pixels = simple_web_render_html_to_pixels_with_engine2d_backend(essentials_page(), W, H, "cpu_simd")
expect(pixels.len()).to_equal(W * H)
step("Header band is exactly #173b7a")
expect(pixel_at(pixels, 200, 10)).to_equal(0xFF173B7Au32)
step("Body ground is exactly #eef2ff")
expect(pixel_at(pixels, 380, 295)).to_equal(0xFFEEF2FFu32)
step("Card background is white (class selector applied)")
expect(pixel_at(pixels, 200, 90)).to_equal(0xFFFFFFFFu32)
step("Button fill is exactly #4f46e5")
expect(pixel_at(pixels, 40, 133)).to_equal(0xFF4F46E5u32)
step("Mark highlight is exactly yellow")
expect(pixel_at(pixels, 117, 103)).to_equal(0xFFFFFF00u32)
step("Anchor text carries blue-dominant pixels")
expect(has_blue_dominant_pixel(pixels, 60, 95, 120, 112)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-001`
- `REQ-WEB-BROWSER-004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `373d93d7444acdfdfcd4541bca05f7d6b4f20a87f2acca1a43a3e51a4cc71f52`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `373d93d7444acdfdfcd4541bca05f7d6b4f20a87f2acca1a43a3e51a4cc71f52`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `373d93d7444acdfdfcd4541bca05f7d6b4f20a87f2acca1a43a3e51a4cc71f52`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/simple_web/feature/web_css_essentials_spec.spl
mirror: doc/06_spec/03_system/app/simple_web/feature/web_css_essentials_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=89; blocker cap makes effective=49
doc/06_spec/03_system/app/simple_web/feature/web_css_essentials_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_web/feature/web_css_essentials_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_web/feature/web_css_essentials_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/simple_web/feature/web_css_essentials_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders header, body ground, card, button, mark, and anchor colors exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
