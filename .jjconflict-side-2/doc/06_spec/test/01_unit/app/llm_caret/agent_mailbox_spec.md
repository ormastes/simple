# Agent Mailbox Specification

> <details>

<!-- sdn-diagram:id=agent_mailbox_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=agent_mailbox_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

agent_mailbox_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=agent_mailbox_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Agent Mailbox Specification

## Scenarios

### LLM Caret agent mailbox

#### routes btw and side messages to an agent inbox

- var mailbox = new agent team mailbox
- mailbox = post btw message
- mailbox = post side message
   - Expected: lead.len() equals `1`
   - Expected: lead[0].channel equals `side`
   - Expected: spark.len() equals `1`
   - Expected: spark[0].channel equals `btw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mailbox = new_agent_team_mailbox("team-1")
mailbox = post_btw_message(mailbox, "lead", "spark", "check docs")
mailbox = post_side_message(mailbox, "spark", "lead", "docs updated")
val lead = agent_team_inbox(mailbox, "lead")
val spark = agent_team_inbox(mailbox, "spark")
expect(lead.len()).to_equal(1)
expect(lead[0].channel).to_equal("side")
expect(spark.len()).to_equal(1)
expect(spark[0].channel).to_equal("btw")
```

</details>

#### keeps transcript order and filters channel

- var mailbox = new agent team mailbox
- mailbox = post btw message
- mailbox = post side message
   - Expected: transcript.len() equals `2`
   - Expected: transcript[0].body equals `shared`
   - Expected: btw.len() equals `1`
   - Expected: haiku.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mailbox = new_agent_team_mailbox("team-1")
mailbox = post_btw_message(mailbox, "lead", "*", "shared")
mailbox = post_side_message(mailbox, "spark", "haiku", "private")
val transcript = agent_team_transcript(mailbox)
val btw = agent_team_channel(mailbox, "btw")
val haiku = agent_team_inbox(mailbox, "haiku")
expect(transcript.len()).to_equal(2)
expect(transcript[0].body).to_equal("shared")
expect(btw.len()).to_equal(1)
expect(haiku.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/agent_mailbox_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLM Caret agent mailbox

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
