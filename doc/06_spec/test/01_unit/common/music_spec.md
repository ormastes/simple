# Music Specification

> <details>

<!-- sdn-diagram:id=music_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=music_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

music_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=music_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Music Specification

## Scenarios

### music{} typed IR

#### lowers minimal score syntax to typed music IR

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val score = music_lower_minimal_score("title: Tiny Etude\nnote C4 quarter m1 s1\nnote D4 half m2 s1\n")

expect(score.title).to_equal("Tiny Etude")
expect(score.notes.len()).to_equal(2)
expect(score.notes[0].pitch).to_equal("C4")
expect(score.notes[0].duration).to_equal("quarter")
expect(score.notes[0].measure).to_equal(1)
expect(score.notes[0].staff).to_equal(1)
expect(score.notes[1].measure).to_equal(2)
```

</details>

### MusicXML 4.0 interchange

#### exports a MusicXML 4.0 score-partwise subset

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val score = music_lower_minimal_score("title: Tiny Etude\nnote C4 quarter m1 s1\n")
val xml = music_score_to_musicxml4(score)

expect(xml).to_contain("<score-partwise version=\"4.0\">")
expect(xml).to_contain("<work-title>Tiny Etude</work-title>")
expect(xml).to_contain("<measure number=\"1\">")
expect(xml).to_contain("<step>C</step>")
expect(xml).to_contain("<octave>4</octave>")
expect(xml).to_contain("<type>quarter</type>")
expect(musicxml4_validate_baseline(xml)).to_equal(true)
```

</details>

#### rejects malformed baseline MusicXML exports

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(musicxml4_validate_baseline("<score-partwise version=\"4.0\"></score-partwise>")).to_equal(false)
```

</details>

#### round-trips pitch, duration, measure, staff, and title metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val score = music_lower_minimal_score("title: Round Trip\nnote C4 quarter m1 s1\nnote E5 half m2 s1\n")
val xml = music_score_to_musicxml4(score)
val imported = musicxml4_import_baseline(xml)

expect(imported.title).to_equal("Round Trip")
expect(imported.notes.len()).to_equal(2)
expect(imported.notes[0].pitch).to_equal("C4")
expect(imported.notes[0].duration).to_equal("quarter")
expect(imported.notes[0].measure).to_equal(1)
expect(imported.notes[0].staff).to_equal(1)
expect(imported.notes[1].pitch).to_equal("E5")
expect(imported.notes[1].duration).to_equal("half")
expect(imported.notes[1].measure).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/music_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- music{} typed IR
- MusicXML 4.0 interchange

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
