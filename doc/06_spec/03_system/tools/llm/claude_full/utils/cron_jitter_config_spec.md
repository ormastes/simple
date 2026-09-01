# Claude Full cron jitter config

> Pure Simple coverage for cron jitter config validation and fallback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full cron jitter config

Pure Simple coverage for cron jitter config validation and fallback.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/cron_jitter_config_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for cron jitter config validation and fallback.

## Scenarios

### Claude full cron jitter config

#### returns TS default config when candidate is absent

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns TS default config when candidate is absent
- Check default fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns TS default config when candidate is absent")
step("Check default fallback")
val config = parseCronJitterConfig(nil)
expectDefaultCronJitterConfig(config)
```

</details>

#### accepts valid config and defaults missing recurring max age

- accepts valid config and defaults missing recurring max age
- Check valid candidate
   - Expected: config.recurringFrac equals `0.5`
   - Expected: config.recurringCapMs equals `120000`
   - Expected: config.oneShotMaxMs equals `300000`
   - Expected: config.oneShotFloorMs equals `30000`
   - Expected: config.oneShotMinuteMod equals `15`
   - Expected: config.recurringMaxAgeMs equals `604800000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts valid config and defaults missing recurring max age")
step("Check valid candidate")
val config = parseCronJitterConfig(Some(CronJitterConfigCandidate(recurringFrac: 0.5, recurringCapMs: 120000, oneShotMaxMs: 300000, oneShotFloorMs: 30000, oneShotMinuteMod: 15, recurringMaxAgeMs: nil)))
expect(config.recurringFrac).to_equal(0.5)
expect(config.recurringCapMs).to_equal(120000)
expect(config.oneShotMaxMs).to_equal(300000)
expect(config.oneShotFloorMs).to_equal(30000)
expect(config.oneShotMinuteMod).to_equal(15)
expect(config.recurringMaxAgeMs).to_equal(604800000)
```

</details>

#### rejects invalid bounds as a whole config

- rejects invalid bounds as a whole config
- Check invalid candidate fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects invalid bounds as a whole config")
step("Check invalid candidate fallback")
val config = parseCronJitterConfig(Some(CronJitterConfigCandidate(recurringFrac: 1.1, recurringCapMs: 120000, oneShotMaxMs: 300000, oneShotFloorMs: 30000, oneShotMinuteMod: 15, recurringMaxAgeMs: Some(1000))))
expectDefaultCronJitterConfig(config)
```

</details>

#### rejects inverted one-shot floor and max

- rejects inverted one-shot floor and max
- Check floor max refine


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects inverted one-shot floor and max")
step("Check floor max refine")
val config = parseCronJitterConfig(Some(CronJitterConfigCandidate(recurringFrac: 0.5, recurringCapMs: 120000, oneShotMaxMs: 1000, oneShotFloorMs: 2000, oneShotMinuteMod: 15, recurringMaxAgeMs: Some(1000))))
expectDefaultCronJitterConfig(config)
```

</details>

#### accepts recurring max age boundaries

- accepts recurring max age boundaries
- Check max age edges
   - Expected: zero.recurringMaxAgeMs equals `0`
   - Expected: thirtyDays.recurringMaxAgeMs equals `2592000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts recurring max age boundaries")
step("Check max age edges")
val zero = parseCronJitterConfig(Some(CronJitterConfigCandidate(recurringFrac: 0.5, recurringCapMs: 120000, oneShotMaxMs: 300000, oneShotFloorMs: 30000, oneShotMinuteMod: 15, recurringMaxAgeMs: Some(0))))
val thirtyDays = parseCronJitterConfig(Some(CronJitterConfigCandidate(recurringFrac: 0.5, recurringCapMs: 120000, oneShotMaxMs: 300000, oneShotFloorMs: 30000, oneShotMinuteMod: 15, recurringMaxAgeMs: Some(2592000000))))
expect(zero.recurringMaxAgeMs).to_equal(0)
expect(thirtyDays.recurringMaxAgeMs).to_equal(2592000000)
```

</details>

#### rejects recurring max age outside boundaries

- rejects recurring max age outside boundaries
- Check max age bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects recurring max age outside boundaries")
step("Check max age bounds")
val negative = parseCronJitterConfig(Some(CronJitterConfigCandidate(recurringFrac: 0.5, recurringCapMs: 120000, oneShotMaxMs: 300000, oneShotFloorMs: 30000, oneShotMinuteMod: 15, recurringMaxAgeMs: Some(-1))))
val tooLarge = parseCronJitterConfig(Some(CronJitterConfigCandidate(recurringFrac: 0.5, recurringCapMs: 120000, oneShotMaxMs: 300000, oneShotFloorMs: 30000, oneShotMinuteMod: 15, recurringMaxAgeMs: Some(2592000001))))
expectDefaultCronJitterConfig(negative)
expectDefaultCronJitterConfig(tooLarge)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `c64dabdbe1fd61cde23701d27f7ff3b8bac2dbde636c604f82b33fe5979810c4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c64dabdbe1fd61cde23701d27f7ff3b8bac2dbde636c604f82b33fe5979810c4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c64dabdbe1fd61cde23701d27f7ff3b8bac2dbde636c604f82b33fe5979810c4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/cron_jitter_config_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/cron_jitter_config_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/cron_jitter_config_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/cron_jitter_config_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/cron_jitter_config_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/cron_jitter_config_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns TS default config when candidate is absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/cron_jitter_config_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts valid config and defaults missing recurring max age' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/cron_jitter_config_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid bounds as a whole config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
