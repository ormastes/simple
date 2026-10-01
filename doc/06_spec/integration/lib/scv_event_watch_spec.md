# scv_event_watch_spec

> Purpose: This spec proves the SCV-IMPL-E-01 event watch layer

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_event_watch_spec

Purpose: This spec proves the SCV-IMPL-E-01 event watch layer

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/integration/lib/scv_event_watch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves the SCV-IMPL-E-01 event watch layer
(`src/lib/nogc_async_mut/file_system/event_watch.spl`): polling detection of
create/modify/delete with monotonic sequence tokens, deterministic test
injection, cookie-based rename pairing, overflow classification (one overflow
event + forced resnapshot), an ignore policy, and an EXPLICITLY failing native
notify bridge (never a silent polling fallback).
Audience: Maintainers of the SCV event layer.

## Scenarios

### scv event watch (E-01)

#### detects create, modify, and delete with monotonic sequence tokens

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects create, modify, and delete with monotonic sequence tokens
- Open a watcher, mutate files, poll, and check kinds + seq order
   - Expected: _kinds(ev1) equals `created`
   - Expected: _kinds(ev2) equals `modified`
   - Expected: _kinds(ev3) equals `deleted`
   - Expected: ev1[0].seq < ev2[0].seq is true
   - Expected: ev2[0].seq < ev3[0].seq is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects create, modify, and delete with monotonic sequence tokens")
step("Open a watcher, mutate files, poll, and check kinds + seq order")
val root = _fixture("cmd")
var state = fswatch_open(root, [])
file_write("{root}/a.txt", "one")
val (s1, ev1) = fswatch_poll(state)
expect(_kinds(ev1)).to_equal("created")
file_write("{root}/a.txt", "longer-content")
val (s2, ev2) = fswatch_poll(s1)
expect(_kinds(ev2)).to_equal("modified")
file_delete("{root}/a.txt")
val (s3, ev3) = fswatch_poll(s2)
expect(_kinds(ev3)).to_equal("deleted")
expect(ev1[0].seq < ev2[0].seq).to_equal(true)
expect(ev2[0].seq < ev3[0].seq).to_equal(true)
dir_remove_all(root)
```

</details>

#### pairs injected rename_from/rename_to events by cookie

- pairs injected rename_from/rename_to events by cookie
- Inject a cookie-matched rename pair plus an unpaired from
   - Expected: paired.len() equals `2`
   - Expected: paired[0].kind equals `renamed`
   - Expected: paired[0].path equals `{root}/new.txt`
   - Expected: paired[0].related equals `{root}/old.txt`
   - Expected: paired[1].kind equals `rename_from`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pairs injected rename_from/rename_to events by cookie")
step("Inject a cookie-matched rename pair plus an unpaired from")
val root = _fixture("ren")
var state = fswatch_open(root, [])
state = fswatch_inject(state, "rename_from", "{root}/old.txt", "cookie-7")
state = fswatch_inject(state, "rename_to", "{root}/new.txt", "cookie-7")
state = fswatch_inject(state, "rename_from", "{root}/lost.txt", "cookie-9")
val (s1, raw) = fswatch_poll(state)
val paired = fswatch_pair_renames(raw)
expect(paired.len()).to_equal(2)
expect(paired[0].kind).to_equal("renamed")
expect(paired[0].path).to_equal("{root}/new.txt")
expect(paired[0].related).to_equal("{root}/old.txt")
expect(paired[1].kind).to_equal("rename_from")
dir_remove_all(root)
```

</details>

#### classifies overflow as a single overflow event and resnapshots

- classifies overflow as a single overflow event and resnapshots
- Mark overflow, poll once for the overflow, poll again clean
   - Expected: _kinds(ev1) equals `overflow`
   - Expected: ev2.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("classifies overflow as a single overflow event and resnapshots")
step("Mark overflow, poll once for the overflow, poll again clean")
val root = _fixture("ovf")
var state = fswatch_open(root, [])
file_write("{root}/lost-while-overflowed.txt", "x")
state = fswatch_inject(state, "created", "{root}/stale-hint.txt", "")
state = fswatch_mark_overflow(state)
val (s1, ev1) = fswatch_poll(state)
expect(_kinds(ev1)).to_equal("overflow")
val (s2, ev2) = fswatch_poll(s1)
expect(ev2.len()).to_equal(0)
dir_remove_all(root)
```

</details>

#### applies the ignore policy to scans and injection

- applies the ignore policy to scans and injection
- Files under an ignored prefix produce no events
   - Expected: ev1.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("applies the ignore policy to scans and injection")
step("Files under an ignored prefix produce no events")
val root = _fixture("ign")
var state = fswatch_open(root, [".scv/"])
dir_create("{root}/.scv/journal", true)
file_write("{root}/.scv/journal/events.log", "internal")
state = fswatch_inject(state, "created", "{root}/.scv/HEAD_OP", "")
val (s1, ev1) = fswatch_poll(state)
expect(ev1.len()).to_equal(0)
dir_remove_all(root)
```

</details>

#### fails the native notify bridge explicitly instead of faking it

- fails the native notify bridge explicitly instead of faking it
- fswatch_native_open reports an ERROR naming the missing bridge
   - Expected: verdict.starts_with("ERROR") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails the native notify bridge explicitly instead of faking it")
step("fswatch_native_open reports an ERROR naming the missing bridge")
val verdict = fswatch_native_open("/tmp")
expect(verdict.starts_with("ERROR")).to_equal(true)
expect(verdict).to_contain("fswatch")
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

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-EVENT-WATCH-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c0f1a95c98d5e40f5a793cd44f68ab5e5c740971f4a57fdd4abb1a72e7f185fe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c0f1a95c98d5e40f5a793cd44f68ab5e5c740971f4a57fdd4abb1a72e7f185fe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c0f1a95c98d5e40f5a793cd44f68ab5e5c740971f4a57fdd4abb1a72e7f185fe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/lib/scv_event_watch_spec.spl
mirror: doc/06_spec/integration/lib/scv_event_watch_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/integration/lib/scv_event_watch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/lib/scv_event_watch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/lib/scv_event_watch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/lib/scv_event_watch_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/lib/scv_event_watch_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects create, modify, and delete with monotonic sequence tokens' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/scv_event_watch_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pairs injected rename_from/rename_to events by cookie' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/scv_event_watch_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies overflow as a single overflow event and resnapshots' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
