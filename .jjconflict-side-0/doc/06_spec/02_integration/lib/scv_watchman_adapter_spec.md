# scv_watchman_adapter_spec

> Purpose: This spec proves the SCV-IMPL-E-08 Watchman adapter behind the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_watchman_adapter_spec

Purpose: This spec proves the SCV-IMPL-E-08 Watchman adapter behind the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/scv_watchman_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves the SCV-IMPL-E-08 Watchman adapter behind the
EventSource protocol (`src/lib/scv/watchman_adapter.spl`): the cursor's
opaque token is the watchman clockspec; file notifications settle on a
logical clock (no sleeping); `is_fresh_instance` and recrawl responses
force the mandatory reconcile path — events are refused until
scv_watchman_reconcile runs. The transport is a deterministic fake-watchman
message queue: no live watchman binary is exercised here (real-binary
integration is an explicit TODO in the module).
Audience: Maintainers of the SCV event layer.

## Scenarios

### scv watchman adapter behind EventSource (E-08)

#### opens with a watchman cursor marked fresh_instance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Open and inspect cursor fields
   - Expected: cur.source equals `watchman`
   - Expected: cur.fresh_instance is true
   - Expected: cur.overflowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-WATCHMAN-ADAPTER-001
step("Open and inspect cursor fields")
val (a, cur) = scv_watchman_open("/repo", 100)
expect(cur.source).to_equal("watchman")
expect(cur.fresh_instance).to_equal(true)
expect(cur.overflowed).to_equal(false)
```

</details>

#### refuses events on a fresh cursor until reconcile runs

- Inject a files message, pull fresh, reconcile, pull again
   - Expected: pull1.needs_rescan is true
   - Expected: pull1.events.len() equals `0`
   - Expected: cur2.fresh_instance is false
   - Expected: pull3.needs_rescan is false
   - Expected: pull3.events.len() equals `1`
   - Expected: pull3.events[0].path equals `a.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-WATCHMAN-ADAPTER-001
step("Inject a files message, pull fresh, reconcile, pull again")
var (a, cur) = scv_watchman_open("/repo", 100)
a = scv_watchman_inject(a, WatchmanMsg(kind: "subscribe_ack", clock: "c:1:1", fresh: false, events: []), 0)
a = scv_watchman_inject(a, _files_msg("c:1:2", "created", "a.txt"), 0)
val (a1, pull1) = scv_watchman_pull(a, cur, 1000)
expect(pull1.needs_rescan).to_equal(true)
expect(pull1.events.len()).to_equal(0)
val (a2, cur2) = scv_watchman_reconcile(a1, cur)
expect(cur2.fresh_instance).to_equal(false)
val (a3, pull3) = scv_watchman_pull(a2, cur2, 1000)
expect(pull3.needs_rescan).to_equal(false)
expect(pull3.events.len()).to_equal(1)
expect(pull3.events[0].path).to_equal("a.txt")
```

</details>

#### carries the watchman clockspec as the opaque token

- Clock advances with delivered messages
   - Expected: cur1.opaque_token equals `c:9:1`
   - Expected: pull2.cursor.opaque_token equals `c:9:7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-WATCHMAN-ADAPTER-001
step("Clock advances with delivered messages")
var (a, cur) = scv_watchman_open("/repo", 100)
a = scv_watchman_inject(a, WatchmanMsg(kind: "subscribe_ack", clock: "c:9:1", fresh: false, events: []), 0)
val (a1, cur1) = scv_watchman_reconcile(a, cur)
expect(cur1.opaque_token).to_equal("c:9:1")
a = scv_watchman_inject(a1, _files_msg("c:9:7", "modified", "b.txt"), 0)
val (a2, pull2) = scv_watchman_pull(a, cur1, 1000)
expect(pull2.cursor.opaque_token).to_equal("c:9:7")
```

</details>

#### settles file events on the logical clock without sleeping

- An event inside the settle window is held; past it, released
   - Expected: early.events.len() equals `0`
   - Expected: early.needs_rescan is false
   - Expected: late.events.len() equals `1`
   - Expected: late.events[0].path equals `hot.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-WATCHMAN-ADAPTER-001
step("An event inside the settle window is held; past it, released")
var (a, cur) = scv_watchman_open("/repo", 100)
val (a0, cur0) = scv_watchman_reconcile(a, cur)
var a1 = scv_watchman_inject(a0, _files_msg("c:1:3", "modified", "hot.txt"), 950)
val (a2, early) = scv_watchman_pull(a1, cur0, 1000)
expect(early.events.len()).to_equal(0)
expect(early.needs_rescan).to_equal(false)
val (a3, late) = scv_watchman_pull(a2, early.cursor, 1050)
expect(late.events.len()).to_equal(1)
expect(late.events[0].path).to_equal("hot.txt")
```

</details>

#### maps is_fresh_instance to the mandatory reconcile path

- A fresh files response invalidates the incremental stream
   - Expected: pull.needs_rescan is true
   - Expected: pull.cursor.overflowed is true
   - Expected: pull.events.len() equals `0`
   - Expected: cur3.overflowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-WATCHMAN-ADAPTER-001
step("A fresh files response invalidates the incremental stream")
var (a, cur) = scv_watchman_open("/repo", 100)
val (a0, cur0) = scv_watchman_reconcile(a, cur)
var a1 = scv_watchman_inject(a0, WatchmanMsg(kind: "files", clock: "c:2:1", fresh: true,
                                             events: [FsWatchEvent(seq: 0, kind: "created", path: "x", related: "")]), 0)
val (a2, pull) = scv_watchman_pull(a1, cur0, 1000)
expect(pull.needs_rescan).to_equal(true)
expect(pull.cursor.overflowed).to_equal(true)
expect(pull.events.len()).to_equal(0)
val (a3, cur3) = scv_watchman_reconcile(a2, pull.cursor)
expect(cur3.overflowed).to_equal(false)
```

</details>

#### maps a recrawl warning to the mandatory reconcile path

- Recrawl ⇒ overflowed cursor, refused events, reconcile clears
   - Expected: pull.needs_rescan is true
   - Expected: pull.cursor.overflowed is true
   - Expected: pull4.needs_rescan is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-WATCHMAN-ADAPTER-001
step("Recrawl ⇒ overflowed cursor, refused events, reconcile clears")
var (a, cur) = scv_watchman_open("/repo", 100)
val (a0, cur0) = scv_watchman_reconcile(a, cur)
var a1 = scv_watchman_inject(a0, WatchmanMsg(kind: "recrawl", clock: "c:3:1", fresh: false, events: []), 0)
a1 = scv_watchman_inject(a1, _files_msg("c:3:2", "modified", "y.txt"), 0)
val (a2, pull) = scv_watchman_pull(a1, cur0, 1000)
expect(pull.needs_rescan).to_equal(true)
expect(pull.cursor.overflowed).to_equal(true)
val (a3, cur3) = scv_watchman_reconcile(a2, pull.cursor)
val (a4, pull4) = scv_watchman_pull(a3, cur3, 2000)
expect(pull4.needs_rescan).to_equal(false)
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

- `REQ-SCV-WATCHMAN-ADAPTER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `944927178b02128ddb9cfa7ba6b444f5eec51af7005637241c362b407c3c9836`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `944927178b02128ddb9cfa7ba6b444f5eec51af7005637241c362b407c3c9836`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `944927178b02128ddb9cfa7ba6b444f5eec51af7005637241c362b407c3c9836`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/lib/scv_watchman_adapter_spec.spl
mirror: doc/06_spec/02_integration/lib/scv_watchman_adapter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/scv_watchman_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/scv_watchman_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/lib/scv_watchman_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/lib/scv_watchman_adapter_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens with a watchman cursor marked fresh_instance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/scv_watchman_adapter_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses events on a fresh cursor until reconcile runs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/scv_watchman_adapter_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries the watchman clockspec as the opaque token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
