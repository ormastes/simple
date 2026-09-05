# Claude Full Buddy Prompt

> Checks companion intro prompt text and attachment gating.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Buddy Prompt

Checks companion intro prompt text and attachment gating.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/buddy/prompt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks companion intro prompt text and attachment gating.

## Scenarios

### Claude full buddy prompt

#### builds companion intro text

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds companion intro text
- Tell the model the companion is separate and should answer tersely


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds companion intro text")
step("Tell the model the companion is separate and should answer tersely")
val text = companionIntroText("Pip", "duck")
expect(text).to_contain("# Companion")
expect(text).to_contain("A small duck named Pip")
expect(text).to_contain(separateWatcherInstruction())
expect(text).to_contain(oneLineInstruction())
```

</details>

#### emits intro attachment only when enabled and not already announced

- emits intro attachment only when enabled and not already announced
- Feature, companion presence, mute flag, and prior attachment gate output
   - Expected: getCompanionIntroAttachment(false, true, false, "Pip", "duck", []).len() equals `0`
   - Expected: getCompanionIntroAttachment(true, false, false, "Pip", "duck", []).len() equals `0`
   - Expected: getCompanionIntroAttachment(true, true, true, "Pip", "duck", []).len() equals `0`
   - Expected: emitted.len() equals `1`
   - Expected: emitted[0].kind equals `companionIntroAttachmentType()`
   - Expected: emitted[0].name equals `Pip`
   - Expected: emitted[0].species equals `duck`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("emits intro attachment only when enabled and not already announced")
step("Feature, companion presence, mute flag, and prior attachment gate output")
expect(getCompanionIntroAttachment(false, true, false, "Pip", "duck", []).len()).to_equal(0)
expect(getCompanionIntroAttachment(true, false, false, "Pip", "duck", []).len()).to_equal(0)
expect(getCompanionIntroAttachment(true, true, true, "Pip", "duck", []).len()).to_equal(0)
val emitted = getCompanionIntroAttachment(true, true, false, "Pip", "duck", [])
expect(emitted.len()).to_equal(1)
expect(emitted[0].kind).to_equal(companionIntroAttachmentType())
expect(emitted[0].name).to_equal("Pip")
expect(emitted[0].species).to_equal("duck")
```

</details>

#### skips duplicate companion intro attachments

- skips duplicate companion intro attachments
- Only matching attachment type and companion name count as announced
   - Expected: alreadyAnnounced("Pip", messages) is true
   - Expected: alreadyAnnounced("Dot", messages) is false
   - Expected: getCompanionIntroAttachment(true, true, false, "Pip", "duck", messages).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips duplicate companion intro attachments")
step("Only matching attachment type and companion name count as announced")
val messages = [CompanionIntroMessage.user(), CompanionIntroMessage.attachment("Pip")]
expect(alreadyAnnounced("Pip", messages)).to_equal(true)
expect(alreadyAnnounced("Dot", messages)).to_equal(false)
expect(getCompanionIntroAttachment(true, true, false, "Pip", "duck", messages).len()).to_equal(0)
```

</details>

#### exports source-backed config names

- exports source-backed config names
- Pin feature and config keys
   - Expected: buddyFeatureName() equals `BUDDY`
   - Expected: companionMutedConfigField() equals `companionMuted`
   - Expected: companionIntroAttachmentType() equals `companion_intro`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed config names")
step("Pin feature and config keys")
expect(buddyFeatureName()).to_equal("BUDDY")
expect(companionMutedConfigField()).to_equal("companionMuted")
expect(companionIntroAttachmentType()).to_equal("companion_intro")
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

- Canonical SPipe generation for source `eda09860673e6572ac972ba15deb1f0876701918ba82d6c23d5a490fd715e941`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eda09860673e6572ac972ba15deb1f0876701918ba82d6c23d5a490fd715e941`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eda09860673e6572ac972ba15deb1f0876701918ba82d6c23d5a490fd715e941`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/buddy/prompt_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/buddy/prompt_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/buddy/prompt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/buddy/prompt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/buddy/prompt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/buddy/prompt_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds companion intro text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/buddy/prompt_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits intro attachment only when enabled and not already announced' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/buddy/prompt_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips duplicate companion intro attachments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
