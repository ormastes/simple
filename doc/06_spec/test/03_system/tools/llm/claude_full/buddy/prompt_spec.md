# Claude Full Buddy Prompt

> Checks companion intro prompt text and attachment gating.

<!-- sdn-diagram:id=prompt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=prompt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

prompt_spec -> std
prompt_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=prompt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks companion intro prompt text and attachment gating.

## Scenarios

### Claude full buddy prompt

#### builds companion intro text

- Tell the model the companion is separate and should answer tersely


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Tell the model the companion is separate and should answer tersely")
val text = companionIntroText("Pip", "duck")
expect(text).to_contain("# Companion")
expect(text).to_contain("A small duck named Pip")
expect(text).to_contain(separateWatcherInstruction())
expect(text).to_contain(oneLineInstruction())
```

</details>

#### emits intro attachment only when enabled and not already announced

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

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Only matching attachment type and companion name count as announced
   - Expected: alreadyAnnounced("Pip", messages) is true
   - Expected: alreadyAnnounced("Dot", messages) is false
   - Expected: getCompanionIntroAttachment(true, true, false, "Pip", "duck", messages).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Only matching attachment type and companion name count as announced")
val messages = [CompanionIntroMessage.user(), CompanionIntroMessage.attachment("Pip")]
expect(alreadyAnnounced("Pip", messages)).to_equal(true)
expect(alreadyAnnounced("Dot", messages)).to_equal(false)
expect(getCompanionIntroAttachment(true, true, false, "Pip", "duck", messages).len()).to_equal(0)
```

</details>

#### exports source-backed config names

- Pin feature and config keys
   - Expected: buddyFeatureName() equals `BUDDY`
   - Expected: companionMutedConfigField() equals `companionMuted`
   - Expected: companionIntroAttachmentType() equals `companion_intro`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
