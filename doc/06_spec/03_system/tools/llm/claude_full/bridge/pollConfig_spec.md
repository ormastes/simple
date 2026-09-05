# Claude Full Bridge Poll Config

> Mirrors GrowthBook poll config validation and fallback behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge Poll Config

Mirrors GrowthBook poll config validation and fallback behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/bridge/pollConfig_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors GrowthBook poll config validation and fallback behavior.

## Scenarios

### Claude full bridge poll config

#### accepts a complete valid GrowthBook poll config

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a complete valid GrowthBook poll config
- Parse required and optional poll intervals
   - Expected: cfg.poll_interval_ms_not_at_capacity equals `150`
   - Expected: cfg.poll_interval_ms_at_capacity equals `250`
   - Expected: cfg.non_exclusive_heartbeat_interval_ms equals `300`
   - Expected: cfg.multisession_poll_interval_ms_not_at_capacity equals `400`
   - Expected: cfg.multisession_poll_interval_ms_partial_capacity equals `500`
   - Expected: cfg.multisession_poll_interval_ms_at_capacity equals `600`
   - Expected: cfg.reclaim_older_than_ms equals `700`
   - Expected: cfg.session_keepalive_interval_v2_ms equals `800`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts a complete valid GrowthBook poll config")
step("Parse required and optional poll intervals")
val cfg = getPollIntervalConfig(PollIntervalConfigCandidate.fromRequired(150, 250).withHeartbeat(300).withMultisession(400, 500, 600).withReclaim(700).withSessionKeepalive(800))
expect(cfg.poll_interval_ms_not_at_capacity).to_equal(150)
expect(cfg.poll_interval_ms_at_capacity).to_equal(250)
expect(cfg.non_exclusive_heartbeat_interval_ms).to_equal(300)
expect(cfg.multisession_poll_interval_ms_not_at_capacity).to_equal(400)
expect(cfg.multisession_poll_interval_ms_partial_capacity).to_equal(500)
expect(cfg.multisession_poll_interval_ms_at_capacity).to_equal(600)
expect(cfg.reclaim_older_than_ms).to_equal(700)
expect(cfg.session_keepalive_interval_v2_ms).to_equal(800)
```

</details>

#### defaults optional fields while preserving required served values

- defaults optional fields while preserving required served values
- Omit zod-defaulted fields
   - Expected: cfg.poll_interval_ms_not_at_capacity equals `1000`
   - Expected: cfg.poll_interval_ms_at_capacity equals `2000`
   - Expected: cfg.non_exclusive_heartbeat_interval_ms equals `0`
   - Expected: cfg.multisession_poll_interval_ms_not_at_capacity equals `2000`
   - Expected: cfg.multisession_poll_interval_ms_partial_capacity equals `2000`
   - Expected: cfg.multisession_poll_interval_ms_at_capacity equals `600000`
   - Expected: cfg.reclaim_older_than_ms equals `5000`
   - Expected: cfg.session_keepalive_interval_v2_ms equals `120000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defaults optional fields while preserving required served values")
step("Omit zod-defaulted fields")
val cfg = getPollIntervalConfig(PollIntervalConfigCandidate.fromRequired(1000, 2000))
expect(cfg.poll_interval_ms_not_at_capacity).to_equal(1000)
expect(cfg.poll_interval_ms_at_capacity).to_equal(2000)
expect(cfg.non_exclusive_heartbeat_interval_ms).to_equal(0)
expect(cfg.multisession_poll_interval_ms_not_at_capacity).to_equal(2000)
expect(cfg.multisession_poll_interval_ms_partial_capacity).to_equal(2000)
expect(cfg.multisession_poll_interval_ms_at_capacity).to_equal(600000)
expect(cfg.reclaim_older_than_ms).to_equal(5000)
expect(cfg.session_keepalive_interval_v2_ms).to_equal(120000)
```

</details>

#### falls back to defaults when a seek-work interval is below the floor

- falls back to defaults when a seek-work interval is below the floor
- Reject fat-fingered values below 100ms
   - Expected: parsed.success is false
   - Expected: cfg.poll_interval_ms_not_at_capacity equals `2000`
   - Expected: zeroOrAtLeast100(0) is true
   - Expected: zeroOrAtLeast100(99) is false
   - Expected: zeroOrAtLeast100(100) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("falls back to defaults when a seek-work interval is below the floor")
step("Reject fat-fingered values below 100ms")
val parsed = parsePollIntervalConfig(PollIntervalConfigCandidate.fromRequired(99, 200))
expect(parsed.success).to_equal(false)
expect(parsed.error).to_contain("not_at_capacity")
val cfg = getPollIntervalConfig(PollIntervalConfigCandidate.fromRequired(99, 200))
expect(cfg.poll_interval_ms_not_at_capacity).to_equal(2000)
expect(zeroOrAtLeast100(0)).to_equal(true)
expect(zeroOrAtLeast100(99)).to_equal(false)
expect(zeroOrAtLeast100(100)).to_equal(true)
```

</details>

#### rejects invalid at-capacity liveness combinations

- rejects invalid at-capacity liveness combinations
- Require heartbeat or at-capacity polling
   - Expected: parsedSingle.success is false
   - Expected: parsedMulti.success is false
   - Expected: validatePollIntervalConfig(getPollIntervalConfig(valid)) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects invalid at-capacity liveness combinations")
step("Require heartbeat or at-capacity polling")
val single = PollIntervalConfigCandidate.fromRequired(100, 0).withMultisession(100, 100, 600)
val parsedSingle = parsePollIntervalConfig(single)
expect(parsedSingle.success).to_equal(false)
expect(parsedSingle.error).to_contain("single-session")
val multi = PollIntervalConfigCandidate.fromRequired(100, 600).withMultisession(100, 100, 0)
val parsedMulti = parsePollIntervalConfig(multi)
expect(parsedMulti.success).to_equal(false)
expect(parsedMulti.error).to_contain("multisession")
val valid = PollIntervalConfigCandidate.fromRequired(100, 0).withHeartbeat(250).withMultisession(100, 100, 0)
expect(validatePollIntervalConfig(getPollIntervalConfig(valid))).to_equal("")
```

</details>

#### exposes flag metadata and validation messages

- exposes flag metadata and validation messages
- Read constants used by the fetch wrapper
   - Expected: pollConfigFlagName() equals `tengu_bridge_poll_interval_config`
   - Expected: pollConfigRefreshMs() equals `300000`
   - Expected: pollConfigMinSeekWorkIntervalMs() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes flag metadata and validation messages")
step("Read constants used by the fetch wrapper")
expect(pollConfigFlagName()).to_equal("tengu_bridge_poll_interval_config")
expect(pollConfigRefreshMs()).to_equal(300000)
expect(pollConfigMinSeekWorkIntervalMs()).to_equal(100)
expect(pollConfigZeroOrAtLeast100Message()).to_contain("100ms")
expect(atCapacityLivenessMessage()).to_contain("at-capacity")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8b3ff40fa2722458d2cfc22d7ba5b222ba5b33362cce718b1f152d9404a7b318`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b3ff40fa2722458d2cfc22d7ba5b222ba5b33362cce718b1f152d9404a7b318`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b3ff40fa2722458d2cfc22d7ba5b222ba5b33362cce718b1f152d9404a7b318`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/bridge/pollConfig_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/bridge/pollConfig_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/bridge/pollConfig_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/bridge/pollConfig_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/bridge/pollConfig_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 19 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/bridge/pollConfig_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a complete valid GrowthBook poll config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/pollConfig_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults optional fields while preserving required served values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/pollConfig_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back to defaults when a seek-work interval is below the floor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
