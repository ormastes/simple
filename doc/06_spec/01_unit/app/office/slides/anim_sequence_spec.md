# anim_sequence_spec

> On-slide animation build sequence spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# anim_sequence_spec

On-slide animation build sequence spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/slides/anim_sequence_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

On-slide animation build sequence spec.

Verifies the per-element build order model in
`app.office.slides.anim_sequence`: click-count, the folded start-time
timeline (onClick / afterPrevious / withPrevious), total build duration,
PowerPoint-like `<p:timing>` XML export, and the plain-text build summary.

Timing convention under test (see anim_sequence.spl docstring for the full
rule): start_i = anchor + delay_ms_i, finish_i = start_i + duration_ms_i,
where anchor is 0 for the first step, the previous step's OWN start time
for "withPrevious", the previous step's finish time for "afterPrevious",
and the running max finish time over all prior steps for "onClick".

Ground truth for the 3-step fixture used throughout (title/bullet1/bullet2):
- title:   onClick,       dur 500, delay 0   -> start 0,   finish 500
- bullet1: afterPrevious, dur 300, delay 100 -> anchor = title finish (500),
  start = 500 + 100 = 600, finish = 600 + 300 = 900
- bullet2: withPrevious,  dur 300, delay 0   -> anchor = bullet1's OWN
  start (600), start = 600 + 0 = 600, finish = 600 + 300 = 900
- click_count = 1 (only title is onClick)
- total_ms = max(500, 900, 900) = 900

## Scenarios

### anim_sequence: click count

#### counts exactly one click for a title-onClick, two-follower build

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = build_fixture()
expect(sequence_click_count(seq)).to_equal(1)
```

</details>

### anim_sequence: folded start-time timeline

#### starts the first onClick step (title) at 0ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = build_fixture()
expect(step_start_time_ms(seq, 0)).to_equal(0)
```

</details>

#### starts the afterPrevious step (bullet1) at 600ms (title finish 500 + own delay 100)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = build_fixture()
expect(step_start_time_ms(seq, 1)).to_equal(600)
```

</details>

#### starts the withPrevious step (bullet2) at the SAME 600ms as bullet1's own start

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = build_fixture()
expect(step_start_time_ms(seq, 2)).to_equal(600)
```

</details>

### anim_sequence: total build duration
_sequence_total_ms is the max finish time across all steps._

#### finishes the whole build at 900ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = build_fixture()
expect(sequence_total_ms(seq)).to_equal(900)
```

</details>

### anim_sequence: PowerPoint-like XML export

#### contains the timing wrapper, both effect names, and a trigger name

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = build_fixture()
val xml = sequence_to_xml(seq)
expect(xml).to_contain("<p:timing")
expect(xml).to_contain("fadeIn")
expect(xml).to_contain("flyIn")
expect(xml).to_contain("onClick")
```

</details>

#### carries duration and delay attributes for the afterPrevious step

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = build_fixture()
val xml = sequence_to_xml(seq)
expect(xml).to_contain("dur=\"300\"")
expect(xml).to_contain("delay=\"100\"")
```

</details>

### anim_sequence: plain-text build summary

#### renders the title line with its computed start and duration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = build_fixture()
val summary = sequence_summary(seq)
expect(summary[0]).to_equal("title fadeIn (entrance, onClick) @0ms +500ms")
```

</details>

#### renders the bullet1 line at its folded 600ms start

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = build_fixture()
val summary = sequence_summary(seq)
expect(summary[1]).to_equal("bullet1 flyIn (entrance, afterPrevious) @600ms +300ms")
```

</details>

### deliberate-fail probe (fixed to green)

#### has the correct total build duration of 900ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = build_fixture()
expect(sequence_total_ms(seq)).to_equal(900)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
