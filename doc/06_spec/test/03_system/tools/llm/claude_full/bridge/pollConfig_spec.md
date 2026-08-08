# Claude Full Bridge Poll Config

> Mirrors GrowthBook poll config validation and fallback behavior.

<!-- sdn-diagram:id=pollConfig_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pollConfig_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pollConfig_spec -> std
pollConfig_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pollConfig_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors GrowthBook poll config validation and fallback behavior.

## Scenarios

### Claude full bridge poll config

#### accepts a complete valid GrowthBook poll config

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

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Reject fat-fingered values below 100ms
   - Expected: parsed.success is false
   - Expected: cfg.poll_interval_ms_not_at_capacity equals `2000`
   - Expected: zeroOrAtLeast100(0) is true
   - Expected: zeroOrAtLeast100(99) is false
   - Expected: zeroOrAtLeast100(100) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Require heartbeat or at-capacity polling
   - Expected: parsedSingle.success is false
   - Expected: parsedMulti.success is false
   - Expected: validatePollIntervalConfig(getPollIntervalConfig(valid)) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Read constants used by the fetch wrapper
   - Expected: pollConfigFlagName() equals `tengu_bridge_poll_interval_config`
   - Expected: pollConfigRefreshMs() equals `300000`
   - Expected: pollConfigMinSeekWorkIntervalMs() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
