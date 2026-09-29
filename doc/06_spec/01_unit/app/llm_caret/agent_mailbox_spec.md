# Agent Mailbox Specification

> Tests covering LLM Caret agent mailbox.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Agent Mailbox Specification

## Scenarios

### LLM Caret agent mailbox

#### routes btw and side messages to an agent inbox

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes btw and side messages to an agent inbox
   - Expected: lead.len() equals `1`
   - Expected: lead[0].channel equals `side`
   - Expected: spark.len() equals `1`
   - Expected: spark[0].channel equals `btw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("routes btw and side messages to an agent inbox")
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

- keeps transcript order and filters channel
   - Expected: transcript.len() equals `2`
   - Expected: transcript[0].body equals `shared`
   - Expected: btw.len() equals `1`
   - Expected: haiku.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps transcript order and filters channel")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLM Caret agent mailbox.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1d9a3723a259357bff12b605152e4b657c3fb04b110797cbe1d5a47b2fc9b04a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1d9a3723a259357bff12b605152e4b657c3fb04b110797cbe1d5a47b2fc9b04a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1d9a3723a259357bff12b605152e4b657c3fb04b110797cbe1d5a47b2fc9b04a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/llm_caret/agent_mailbox_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/agent_mailbox_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/agent_mailbox_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/agent_mailbox_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/agent_mailbox_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/agent_mailbox_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes btw and side messages to an agent inbox' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/agent_mailbox_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps transcript order and filters channel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
