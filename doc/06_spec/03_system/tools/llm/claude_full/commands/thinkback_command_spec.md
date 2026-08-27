# Claude Full Thinkback Command

> Checks thinkback command parity with modern SSpec coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Thinkback Command

Checks thinkback command parity with modern SSpec coverage.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/thinkback_command_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks thinkback command parity with modern SSpec coverage.

## Scenarios

### Claude full thinkback command

#### normalizes topics and empty input

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- normalizes topics and empty input
- Normalize topic text
   - Expected: normalizeThinkbackTopic("  Release Plan  ") equals `release plan`
- Use the default empty topic
   - Expected: normalizeThinkbackTopic("   ") equals `recent conversation`
   - Expected: call("   ").topic equals `recent conversation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normalizes topics and empty input")
step("Normalize topic text")
expect(normalizeThinkbackTopic("  Release Plan  ")).to_equal("release plan")

step("Use the default empty topic")
expect(normalizeThinkbackTopic("   ")).to_equal("recent conversation")
expect(call("   ").topic).to_equal("recent conversation")
```

</details>

#### renders replay and summary text

- renders replay and summary text
- Render summary
   - Expected: thinkbackSummaryText("Feature Flags") equals `Thinkback summary: feature flags`
- Render replay
   - Expected: replay.status equals `replay`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders replay and summary text")
step("Render summary")
expect(thinkbackSummaryText("Feature Flags")).to_equal("Thinkback summary: feature flags")
expect(call("Feature Flags").summary).to_contain("feature flags")

step("Render replay")
val replay = callThinkback("Incident Review", "replay")
expect(replay.status).to_equal("replay")
expect(replay.replay).to_contain("incident review")
expect(thinkbackReplayText("Incident Review")).to_start_with("Replay prior context")
```

</details>

#### models selection and installer state

- models selection and installer state
- Select a supported action
   - Expected: selected.selectedAction equals `replay`
- Install and disable states
   - Expected: isDisabled(disabled) is true
   - Expected: ThinkbackInstaller(disabled).status equals `installed`
   - Expected: ThinkbackInstaller(disabled).state.installed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models selection and installer state")
step("Select a supported action")
val state = ThinkbackState.new("Roadmap", "", true, false, ["older"])
val selected = selectThinkbackAction(state, " replay ")
expect(selected.selectedAction).to_equal("replay")
expect(selected.history).to_contain("older")

step("Install and disable states")
val disabled = ThinkbackState.new("Roadmap", "summary", false, true, [])
expect(isDisabled(disabled)).to_equal(true)
expect(errorMsg(disabled)).to_contain("not installed")
expect(ThinkbackInstaller(disabled).status).to_equal("installed")
expect(ThinkbackInstaller(disabled).state.installed).to_equal(true)
```

</details>

#### keeps metadata and source floors visible

- keeps metadata and source floors visible
- Check command metadata
   - Expected: thinkbackIndexName() equals `thinkback`
   - Expected: getMarketplaceName() equals `thinkback`
   - Expected: getMarketplaceRepo() equals `anthropics/thinkback`
   - Expected: getPluginId() equals `anthropic/thinkback`
   - Expected: getThinkbackSkillDir() equals `skills/thinkback`
   - Expected: thinkbackPlugin() equals `anthropic/thinkback`
- Check modeled source line helpers
   - Expected: thinkbackIndexSourceLinesModeled() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps metadata and source floors visible")
step("Check command metadata")
expect(thinkbackIndexName()).to_equal("thinkback")
expect(thinkbackPrompt("latest decision")).to_contain("latest decision")
expect(getMarketplaceName()).to_equal("thinkback")
expect(getMarketplaceRepo()).to_equal("anthropics/thinkback")
expect(getPluginId()).to_equal("anthropic/thinkback")
expect(getThinkbackSkillDir()).to_equal("skills/thinkback")
expect(thinkbackPlugin()).to_equal("anthropic/thinkback")

step("Check modeled source line helpers")
expect(thinkbackIndexSourceLinesModeled()).to_equal(13)
expect(thinkbackSourceLinesModeled()).to_be_greater_than(552)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `32fa362cc349e9e425f10f63982cdd5ef32c018e4e47b3842b703d5adf438673`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `32fa362cc349e9e425f10f63982cdd5ef32c018e4e47b3842b703d5adf438673`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `32fa362cc349e9e425f10f63982cdd5ef32c018e4e47b3842b703d5adf438673`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/commands/thinkback_command_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/thinkback_command_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/thinkback_command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/thinkback_command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/thinkback_command_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/commands/thinkback_command_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes topics and empty input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/thinkback_command_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders replay and summary text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/thinkback_command_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models selection and installer state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
