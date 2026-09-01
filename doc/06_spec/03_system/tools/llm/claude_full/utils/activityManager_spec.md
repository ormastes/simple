# Claude Full Utils ActivityManager

> Mirrors `utils/activityManager.ts` active-time precedence and operation dedupe.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `utils/activityManager.ts` active-time precedence and operation dedupe.

## Scenarios

### Claude full utils ActivityManager

#### records user activity only within the timeout window

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records user activity only within the timeout window
- First activity only seeds the timestamp
   - Expected: manager.getActiveTimeCounter().count() equals `0`
- A later user event inside five seconds records active user time
   - Expected: manager.getActiveTimeCounter().count() equals `1`
   - Expected: manager.getActiveTimeCounter().lastType() equals `user`
   - Expected: manager.getActiveTimeCounter().lastSeconds() equals `2.5`
- Timeout-window gaps update the timestamp without adding metrics
   - Expected: manager.getActiveTimeCounter().count() equals `1`
   - Expected: activityManagerDefaultTimeoutMs() equals `5000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records user activity only within the timeout window")
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

- gives CLI activity precedence and deduplicates repeated operation ids
- Overlapping CLI operations record one interval at the final end
   - Expected: manager.getActiveTimeCounter().count() equals `0`
   - Expected: manager.activeOperationCount() equals `1`
   - Expected: manager.getActivityStates().isCLIActive is true
   - Expected: manager.getActivityStates().activeOperationCount equals `2`
   - Expected: manager.getActiveTimeCounter().count() equals `1`
   - Expected: manager.getActiveTimeCounter().count() equals `2`
   - Expected: manager.getActiveTimeCounter().totalFor("cli") equals `9.0`
   - Expected: manager.getActivityStates().isCLIActive is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gives CLI activity precedence and deduplicates repeated operation ids")
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

- tracks operation wrappers and singleton helpers
- trackOperation records elapsed CLI time and singleton helpers replace state
   - Expected: manager.trackOperation("debug", 750) equals `resolved`
   - Expected: manager.getActiveTimeCounter().lastType() equals `cli`
   - Expected: manager.getActiveTimeCounter().lastSeconds() equals `0.75`
   - Expected: first.getNow() equals `0`
   - Expected: second.getNow() equals `42`
   - Expected: activityManagerSourceLinesModeled() equals `164`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks operation wrappers and singleton helpers")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `da51df63847a1f7d072049f5a2c1125959a9acfdeda1ba4d4d450a3f5d8da078`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da51df63847a1f7d072049f5a2c1125959a9acfdeda1ba4d4d450a3f5d8da078`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da51df63847a1f7d072049f5a2c1125959a9acfdeda1ba4d4d450a3f5d8da078`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/activityManager_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/activityManager_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/activityManager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/activityManager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/activityManager_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/activityManager_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records user activity only within the timeout window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/activityManager_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives CLI activity precedence and deduplicates repeated operation ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/activityManager_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks operation wrappers and singleton helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
