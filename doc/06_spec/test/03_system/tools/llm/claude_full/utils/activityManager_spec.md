# Claude Full Utils ActivityManager

> Mirrors `utils/activityManager.ts` active-time precedence and operation dedupe.

<!-- sdn-diagram:id=activityManager_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=activityManager_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

activityManager_spec -> std
activityManager_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=activityManager_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Utils ActivityManager

Mirrors `utils/activityManager.ts` active-time precedence and operation dedupe.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/activityManager_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `utils/activityManager.ts` active-time precedence and operation dedupe.

## Scenarios

### Claude full utils ActivityManager

#### records user activity only within the timeout window

- First activity only seeds the timestamp
- manager recordUserActivity
   - Expected: manager.getActiveTimeCounter().count() equals `0`
- A later user event inside five seconds records active user time
- manager setNow
- manager recordUserActivity
   - Expected: manager.getActiveTimeCounter().count() equals `1`
   - Expected: manager.getActiveTimeCounter().lastType() equals `user`
   - Expected: manager.getActiveTimeCounter().lastSeconds() equals `2.5`
- Timeout-window gaps update the timestamp without adding metrics
- manager setNow
- manager recordUserActivity
   - Expected: manager.getActiveTimeCounter().count() equals `1`
   - Expected: activityManagerDefaultTimeoutMs() equals `5000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("First activity only seeds the timestamp")
val manager = activityManagerNew(1000)
manager.recordUserActivity()
expect(manager.getActiveTimeCounter().count()).to_equal(0)

step("A later user event inside five seconds records active user time")
manager.setNow(3500)
manager.recordUserActivity()
expect(manager.getActiveTimeCounter().count()).to_equal(1)
expect(manager.getActiveTimeCounter().lastType()).to_equal("user")
expect(manager.getActiveTimeCounter().lastSeconds()).to_equal(2.5)

step("Timeout-window gaps update the timestamp without adding metrics")
manager.setNow(9500)
manager.recordUserActivity()
expect(manager.getActiveTimeCounter().count()).to_equal(1)
expect(activityManagerDefaultTimeoutMs()).to_equal(5000)
```

</details>

#### gives CLI activity precedence and deduplicates repeated operation ids

- Overlapping CLI operations record one interval at the final end
- manager startCLIActivity
- manager setNow
- manager recordUserActivity
   - Expected: manager.getActiveTimeCounter().count() equals `0`
- manager startCLIActivity
   - Expected: manager.activeOperationCount() equals `1`
- manager setNow
- manager startCLIActivity
   - Expected: manager.getActivityStates().isCLIActive is true
   - Expected: manager.getActivityStates().activeOperationCount equals `2`
- manager setNow
- manager endCLIActivity
   - Expected: manager.getActiveTimeCounter().count() equals `1`
- manager setNow
- manager endCLIActivity
   - Expected: manager.getActiveTimeCounter().count() equals `2`
   - Expected: manager.getActiveTimeCounter().totalFor("cli") equals `9.0`
   - Expected: manager.getActivityStates().isCLIActive is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Overlapping CLI operations record one interval at the final end")
val manager = activityManagerNew(10000)
manager.startCLIActivity("tool")
manager.setNow(11000)
manager.recordUserActivity()
expect(manager.getActiveTimeCounter().count()).to_equal(0)
manager.startCLIActivity("tool")
expect(manager.activeOperationCount()).to_equal(1)
manager.setNow(14000)
manager.startCLIActivity("other")
expect(manager.getActivityStates().isCLIActive).to_equal(true)
expect(manager.getActivityStates().activeOperationCount).to_equal(2)
manager.setNow(16000)
manager.endCLIActivity("tool")
expect(manager.getActiveTimeCounter().count()).to_equal(1)
manager.setNow(19000)
manager.endCLIActivity("other")
expect(manager.getActiveTimeCounter().count()).to_equal(2)
expect(manager.getActiveTimeCounter().totalFor("cli")).to_equal(9.0)
expect(manager.getActivityStates().isCLIActive).to_equal(false)
```

</details>

#### tracks operation wrappers and singleton helpers

- trackOperation records elapsed CLI time and singleton helpers replace state
   - Expected: manager.trackOperation("debug", 750) equals `resolved`
   - Expected: manager.getActiveTimeCounter().lastType() equals `cli`
   - Expected: manager.getActiveTimeCounter().lastSeconds() equals `0.75`
- activityManagerResetInstance
   - Expected: first.getNow() equals `0`
   - Expected: second.getNow() equals `42`
   - Expected: activityManagerSourceLinesModeled() equals `164`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("trackOperation records elapsed CLI time and singleton helpers replace state")
val manager = activityManagerNew(2000)
expect(manager.trackOperation("debug", 750)).to_equal("resolved")
expect(manager.getActiveTimeCounter().lastType()).to_equal("cli")
expect(manager.getActiveTimeCounter().lastSeconds()).to_equal(0.75)

activityManagerResetInstance()
val first = activityManagerGetInstance()
expect(first.getNow()).to_equal(0)
val second = activityManagerCreateInstance(42)
expect(second.getNow()).to_equal(42)
expect(activityManagerSourceLinesModeled()).to_equal(164)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
