# Claude Full bash sleep spec

> Pure Simple coverage for sleep command metadata.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full bash sleep spec

Pure Simple coverage for sleep command metadata.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/bash/specs/sleep_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for sleep command metadata.

## Scenarios

### Claude full bash sleep command spec

#### exposes sleep command metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes sleep command metadata
- Check command metadata
   - Expected: spec.name equals `sleep`
   - Expected: spec.description equals `Delay for a specified amount of time`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes sleep command metadata")
step("Check command metadata")
val spec = sleepCommandSpec()
expect(spec.name).to_equal("sleep")
expect(spec.description).to_equal("Delay for a specified amount of time")
```

</details>

#### exposes required duration args

- exposes required duration args
- Check arg metadata
   - Expected: args.name equals `duration`
   - Expected: args.description equals `Duration to sleep (seconds or with suffix like 5s, 2m, 1h)`
   - Expected: args.isOptional equals `Some(false)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes required duration args")
step("Check arg metadata")
val spec = sleepCommandSpec()
if val args = spec.args:
    expect(args.name).to_equal("duration")
    expect(args.description).to_equal("Duration to sleep (seconds or with suffix like 5s, 2m, 1h)")
    expect(args.isOptional).to_equal(Some(false))
    expect(args.isVariadic).to_be_nil()
    expect(args.isCommand).to_be_nil()
else:
    expect(false).to_equal(true)
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4a36f0312763c626a30d0ff38964980f15d0b337f8e712396583ee1597f02191`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4a36f0312763c626a30d0ff38964980f15d0b337f8e712396583ee1597f02191`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4a36f0312763c626a30d0ff38964980f15d0b337f8e712396583ee1597f02191`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/tools/llm/claude_full/utils/bash/specs/sleep_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/bash/specs/sleep_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/bash/specs/sleep_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/bash/specs/sleep_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/bash/specs/sleep_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes sleep command metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/bash/specs/sleep_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes required duration args' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
