# Claude Full context window upgrade check

> Pure Simple coverage for 1M-context upgrade messaging.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full context window upgrade check

Pure Simple coverage for 1M-context upgrade messaging.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/model/contextWindowUpgradeCheck_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for 1M-context upgrade messaging.

## Scenarios

### Claude full context window upgrade check

#### returns nil when no 1M upgrade is available

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns nil when no 1M upgrade is available
- Check unavailable upgrade


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns nil when no 1M upgrade is available")
step("Check unavailable upgrade")
expect(getAvailableUpgrade("haiku", true, true, false)).to_be_nil()
expect(getAvailableUpgrade("opus", false, false, false)).to_be_nil()
expect(getAvailableUpgrade("sonnet", false, false, false)).to_be_nil()
expect(getUpgradeMessage("haiku", true, true, false, "warning")).to_be_nil()
expect(getUpgradeMessage("opus", false, false, false, "tip")).to_be_nil()
```

</details>

#### returns nil when the model already uses 1M context

- returns nil when the model already uses 1M context
- Check max-context models


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns nil when the model already uses 1M context")
step("Check max-context models")
expect(getAvailableUpgrade("opus[1m]", true, true, false)).to_be_nil()
expect(getAvailableUpgrade("claude-sonnet-4-6[1M]", true, true, false)).to_be_nil()
```

</details>

#### formats Opus upgrade messages

- formats Opus upgrade messages
- Check Opus upgrade messages
   - Expected: value.alias equals `opus[1m]`
   - Expected: value.name equals `Opus 1M`
   - Expected: value.multiplier equals `5`
   - Expected: false is true
   - Expected: getUpgradeMessage("opus", true, false, false, "warning") equals `Some("/model opus[1m]")`
   - Expected: getUpgradeMessage("opus", true, false, false, "tip") equals `Some("Tip: You have access to Opus 1M with 5x more context")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats Opus upgrade messages")
step("Check Opus upgrade messages")
val upgrade = getAvailableUpgrade("opus", true, false, false)
if val Some(value) = upgrade:
    expect(value.alias).to_equal("opus[1m]")
    expect(value.name).to_equal("Opus 1M")
    expect(value.multiplier).to_equal(5)
else:
    expect(false).to_equal(true)
expect(getUpgradeMessage("opus", true, false, false, "warning")).to_equal(Some("/model opus[1m]"))
expect(getUpgradeMessage("opus", true, false, false, "tip")).to_equal(Some("Tip: You have access to Opus 1M with 5x more context"))
```

</details>

#### uses merge-enabled Opus access and Sonnet access

- uses merge-enabled Opus access and Sonnet access
- Check access gates
   - Expected: getUpgradeMessage("claude-opus-4-6", false, false, true, "warning") equals `Some("/model opus[1m]")`
   - Expected: value.alias equals `sonnet[1m]`
   - Expected: value.name equals `Sonnet 1M`
   - Expected: value.multiplier equals `5`
   - Expected: false is true
   - Expected: getUpgradeMessage("claude-sonnet-4-6", false, true, false, "warning") equals `Some("/model sonnet[1m]")`
   - Expected: getUpgradeMessage("claude-sonnet-4-6", false, true, false, "tip") equals `Some("Tip: You have access to Sonnet 1M with 5x more context")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses merge-enabled Opus access and Sonnet access")
step("Check access gates")
expect(getUpgradeMessage("claude-opus-4-6", false, false, true, "warning")).to_equal(Some("/model opus[1m]"))
val sonnet = getAvailableUpgrade("claude-sonnet-4-6", false, true, false)
if val Some(value) = sonnet:
    expect(value.alias).to_equal("sonnet[1m]")
    expect(value.name).to_equal("Sonnet 1M")
    expect(value.multiplier).to_equal(5)
else:
    expect(false).to_equal(true)
expect(getUpgradeMessage("claude-sonnet-4-6", false, true, false, "warning")).to_equal(Some("/model sonnet[1m]"))
expect(getUpgradeMessage("claude-sonnet-4-6", false, true, false, "tip")).to_equal(Some("Tip: You have access to Sonnet 1M with 5x more context"))
expect(getUpgradeMessage("claude-sonnet-4-6", false, false, true, "warning")).to_be_nil()
```

</details>

#### returns nil for unknown message contexts

- returns nil for unknown message contexts
- Check unknown context


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns nil for unknown message contexts")
step("Check unknown context")
expect(getUpgradeMessage("sonnet", false, true, false, "other")).to_be_nil()
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

- Canonical SPipe generation for source `ced3093fbe5a32c01497fc0d649df9a2845d7e7c96424d91361524b628bbb13c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ced3093fbe5a32c01497fc0d649df9a2845d7e7c96424d91361524b628bbb13c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ced3093fbe5a32c01497fc0d649df9a2845d7e7c96424d91361524b628bbb13c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/model/contextWindowUpgradeCheck_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/model/contextWindowUpgradeCheck_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/model/contextWindowUpgradeCheck_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/model/contextWindowUpgradeCheck_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/model/contextWindowUpgradeCheck_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/model/contextWindowUpgradeCheck_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil when no 1M upgrade is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/model/contextWindowUpgradeCheck_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil when the model already uses 1M context' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/model/contextWindowUpgradeCheck_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats Opus upgrade messages' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
