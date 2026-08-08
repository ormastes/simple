# Claude Full Session and Status Commands

> Checks modern SSpec parity for session, skills, stats, status, statusline, and stickers.

<!-- sdn-diagram:id=session_status_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=session_status_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

session_status_spec -> std
session_status_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=session_status_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Session and Status Commands

Checks modern SSpec parity for session, skills, stats, status, statusline, and stickers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/session_status_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for session, skills, stats, status, statusline, and stickers.

## Scenarios

### Claude full session status commands

#### should model session display

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = SessionSummary.new("s1", "Build", 4)
expect(sessionIndexName()).to_equal("session")
expect(sessionDisplay(summary)).to_contain("Build")
expect(sessionDisplay(summary)).to_contain("4")
```

</details>

#### should expose small command names

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(skillsIndexName()).to_equal("skills")
expect(statsIndexName()).to_equal("stats")
expect(statusIndexName()).to_equal("status")
expect(statuslineText("model", "/tmp")).to_contain("/tmp")
expect(stickersIndexName()).to_equal("stickers")
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sessionSourceLinesModeled()).to_equal(139)
expect(sessionIndexSourceLinesModeled()).to_equal(16)
expect(skillsSourceLinesModeled()).to_equal(7)
expect(skillsIndexSourceLinesModeled()).to_equal(10)
expect(statsSourceLinesModeled()).to_equal(6)
expect(statsIndexSourceLinesModeled()).to_equal(10)
expect(statusSourceLinesModeled()).to_equal(7)
expect(statusIndexSourceLinesModeled()).to_equal(12)
expect(statuslineSourceLinesModeled()).to_equal(23)
expect(stickersIndexSourceLinesModeled()).to_equal(11)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
