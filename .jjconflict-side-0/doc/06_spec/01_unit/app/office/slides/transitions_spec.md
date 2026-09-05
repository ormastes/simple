# transitions_spec

> Slide transition + auto-advance timing spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# transitions_spec

Slide transition + auto-advance timing spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/slides/transitions_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Slide transition + auto-advance timing spec.

Verifies the presentation timeline model in `app.office.slides.transitions`:
total auto-run duration, count of auto-advancing slides, PowerPoint
`<p:transition>` XML export per slide, and the plain-text timeline summary.

## Scenarios

### transitions: timeline totals

#### computes the total auto-run duration across all slides

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val intro = timing_new("Intro", "fade", 500, 3000)
val body = timing_new("Body", "push", 800, 0)
val end_slide = timing_new("End", "wipe", 1000, 5000)
var timeline = timeline_new()
timeline = timeline_add(timeline, intro)
timeline = timeline_add(timeline, body)
timeline = timeline_add(timeline, end_slide)
expect(timeline_total_ms(timeline)).to_equal(10300)
```

</details>

#### counts only slides with advance_ms > 0 as auto-advancing

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val intro = timing_new("Intro", "fade", 500, 3000)
val body = timing_new("Body", "push", 800, 0)
val end_slide = timing_new("End", "wipe", 1000, 5000)
var timeline = timeline_new()
timeline = timeline_add(timeline, intro)
timeline = timeline_add(timeline, body)
timeline = timeline_add(timeline, end_slide)
expect(timeline_auto_slides(timeline)).to_equal(2)
```

</details>

### transitions: PowerPoint XML export

#### renders a fade transition with fast speed and advTm for a 3000ms advance

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val intro = timing_new("Intro", "fade", 500, 3000)
val xml = timing_to_pptx_xml(intro)
expect(xml).to_contain("<p:transition")
expect(xml).to_contain("spd=\"fast\"")
expect(xml).to_contain("<p:fade")
expect(xml).to_contain("advTm=\"3000\"")
```

</details>

#### renders empty XML for a 'none' transition

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val silent = timing_new("Blank", "none", 0, 0)
val xml = timing_to_pptx_xml(silent)
expect(xml).to_equal("")
```

</details>

#### omits advTm entirely when advance_ms is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = timing_new("Body", "push", 800, 0)
val xml = timing_to_pptx_xml(body)
expect(xml.find("advTm") < 0).to_equal(true)
```

</details>

### transitions: plain-text summary
_`timeline_summary` renders one human-readable line per slide._

#### renders the first slide's summary line with title, transition, and timings

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val intro = timing_new("Intro", "fade", 500, 3000)
val body = timing_new("Body", "push", 800, 0)
var timeline = timeline_new()
timeline = timeline_add(timeline, intro)
timeline = timeline_add(timeline, body)
val summary = timeline_summary(timeline)
expect(summary[0]).to_equal("Intro: fade 500ms advance=3000ms")
```

</details>

### deliberate-fail probe (fixed to green)

#### has exactly two auto-advancing slides in the timeline

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val intro = timing_new("Intro", "fade", 500, 3000)
val body = timing_new("Body", "push", 800, 0)
val end_slide = timing_new("End", "wipe", 1000, 5000)
var timeline = timeline_new()
timeline = timeline_add(timeline, intro)
timeline = timeline_add(timeline, body)
timeline = timeline_add(timeline, end_slide)
expect(timeline_auto_slides(timeline)).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
