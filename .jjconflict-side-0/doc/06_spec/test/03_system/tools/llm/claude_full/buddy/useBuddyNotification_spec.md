# Claude Full Buddy Notification

> Checks buddy teaser date gates, notification decision, rainbow text, and trigger scanning.

<!-- sdn-diagram:id=useBuddyNotification_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=useBuddyNotification_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

useBuddyNotification_spec -> std
useBuddyNotification_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=useBuddyNotification_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Buddy Notification

Checks buddy teaser date gates, notification decision, rainbow text, and trigger scanning.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/buddy/useBuddyNotification_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks buddy teaser date gates, notification decision, rainbow text, and trigger scanning.

## Scenarios

### Claude full buddy notification

#### evaluates teaser and live date gates

- April 1-7 2026 is teaser; command is live from April 2026 onward
   - Expected: isBuddyTeaserWindow(2026, 3, 1, false) is true
   - Expected: isBuddyTeaserWindow(2026, 3, 7, false) is true
   - Expected: isBuddyTeaserWindow(2026, 3, 8, false) is false
   - Expected: isBuddyTeaserWindow(2025, 3, 1, false) is false
   - Expected: isBuddyTeaserWindow(2025, 0, 1, true) is true
   - Expected: isBuddyLive(2026, 2, false) is false
   - Expected: isBuddyLive(2026, 3, false) is true
   - Expected: isBuddyLive(2027, 0, false) is true
   - Expected: isBuddyLive(2025, 0, true) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("April 1-7 2026 is teaser; command is live from April 2026 onward")
expect(isBuddyTeaserWindow(2026, 3, 1, false)).to_equal(true)
expect(isBuddyTeaserWindow(2026, 3, 7, false)).to_equal(true)
expect(isBuddyTeaserWindow(2026, 3, 8, false)).to_equal(false)
expect(isBuddyTeaserWindow(2025, 3, 1, false)).to_equal(false)
expect(isBuddyTeaserWindow(2025, 0, 1, true)).to_equal(true)
expect(isBuddyLive(2026, 2, false)).to_equal(false)
expect(isBuddyLive(2026, 3, false)).to_equal(true)
expect(isBuddyLive(2027, 0, false)).to_equal(true)
expect(isBuddyLive(2025, 0, true)).to_equal(true)
```

</details>

#### decides when to show startup teaser notification

- Feature flag, no companion, and teaser window are required
   - Expected: buddyNotificationDecision(false, false, true).shouldAdd is false
   - Expected: buddyNotificationDecision(true, true, true).shouldAdd is false
   - Expected: buddyNotificationDecision(true, false, false).shouldAdd is false
   - Expected: decision.shouldAdd is true
   - Expected: decision.shouldRemoveOnCleanup is true
   - Expected: decision.key equals `buddyTeaserKey()`
   - Expected: decision.text equals `buddyCommandText()`
   - Expected: decision.priority equals `immediatePriority()`
   - Expected: decision.timeoutMs equals `buddyTeaserTimeoutMs()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Feature flag, no companion, and teaser window are required")
expect(buddyNotificationDecision(false, false, true).shouldAdd).to_equal(false)
expect(buddyNotificationDecision(true, true, true).shouldAdd).to_equal(false)
expect(buddyNotificationDecision(true, false, false).shouldAdd).to_equal(false)
val decision = buddyNotificationDecision(true, false, true)
expect(decision.shouldAdd).to_equal(true)
expect(decision.shouldRemoveOnCleanup).to_equal(true)
expect(decision.key).to_equal(buddyTeaserKey())
expect(decision.text).to_equal(buddyCommandText())
expect(decision.priority).to_equal(immediatePriority())
expect(decision.timeoutMs).to_equal(buddyTeaserTimeoutMs())
```

</details>

#### renders rainbow text spans

- Each character gets a stable color by index
   - Expected: spans.len() equals `6`
   - Expected: spans[0].ch equals `/`
   - Expected: spans[0].color equals `rainbowColor(0)`
   - Expected: spans[5].ch equals `y`
   - Expected: rainbowColors().len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Each character gets a stable color by index")
val spans = rainbowText("/buddy")
expect(spans.len()).to_equal(6)
expect(spans[0].ch).to_equal("/")
expect(spans[0].color).to_equal(rainbowColor(0))
expect(spans[5].ch).to_equal("y")
expect(rainbowColors().len()).to_equal(6)
```

</details>

#### finds slash buddy trigger positions with word boundary

- Match /buddy but not /buddySuffix when feature is enabled
   - Expected: findBuddyTriggerPositions(false, "/buddy").len() equals `0`
   - Expected: hits.len() equals `2`
   - Expected: hits[0].start equals `4`
   - Expected: hits[0].end equals `10`
   - Expected: hits[1].start equals `31`
   - Expected: startsBuddyTriggerAt("/buddy_now", 0) is false
   - Expected: startsBuddyTriggerAt("/buddy!", 0) is true
   - Expected: isWordChar("_") is true
   - Expected: isWordChar("!") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Match /buddy but not /buddySuffix when feature is enabled")
expect(findBuddyTriggerPositions(false, "/buddy").len()).to_equal(0)
val hits = findBuddyTriggerPositions(true, "try /buddy then /buddy_now and /buddy!")
expect(hits.len()).to_equal(2)
expect(hits[0].start).to_equal(4)
expect(hits[0].end).to_equal(10)
expect(hits[1].start).to_equal(31)
expect(startsBuddyTriggerAt("/buddy_now", 0)).to_equal(false)
expect(startsBuddyTriggerAt("/buddy!", 0)).to_equal(true)
expect(isWordChar("_")).to_equal(true)
expect(isWordChar("!")).to_equal(false)
```

</details>

#### exports source-backed constants

- Pin feature name, launch window, cleanup key, and hook notes
   - Expected: buddyFeatureName() equals `BUDDY`
   - Expected: teaserStartYear() equals `2026`
   - Expected: teaserStartMonthZeroBased() equals `3`
   - Expected: teaserEndDayInclusive() equals `7`
   - Expected: commandLiveForeverAfterLaunch() is true
   - Expected: notificationShownWhenNoCompanion() is true
   - Expected: idlePresenceHandledByCompanionSprite() is true
   - Expected: cleanupRemovesKey() equals `buddy-teaser`
   - Expected: effectDependencyCount() equals `2`
   - Expected: compilerMemoSlots() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin feature name, launch window, cleanup key, and hook notes")
expect(buddyFeatureName()).to_equal("BUDDY")
expect(teaserStartYear()).to_equal(2026)
expect(teaserStartMonthZeroBased()).to_equal(3)
expect(teaserEndDayInclusive()).to_equal(7)
expect(localDateWindowReason()).to_contain("timezones")
expect(commandLiveForeverAfterLaunch()).to_equal(true)
expect(notificationShownWhenNoCompanion()).to_equal(true)
expect(idlePresenceHandledByCompanionSprite()).to_equal(true)
expect(triggerRegexSource()).to_contain("buddy")
expect(cleanupRemovesKey()).to_equal("buddy-teaser")
expect(effectDependencyCount()).to_equal(2)
expect(compilerMemoSlots()).to_equal(4)
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
