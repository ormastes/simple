# scv_event_coalesce_spec

> Purpose: This spec proves the SCV-IMPL-E-04 coalescer/settle layer

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_event_coalesce_spec

Purpose: This spec proves the SCV-IMPL-E-04 coalescer/settle layer

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/integration/lib/scv_event_coalesce_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves the SCV-IMPL-E-04 coalescer/settle layer
(`src/lib/scv/event_coalesce.spl`): per-class windows — editor micro-batch,
fs settle window, save flushed immediately, VCS/bulk deferred until an
explicit bulk end — plus dedupe of repeated modifies per path and
atomic-save normalization: tmp-write + rename-to-target (+ tmp delete)
coalesces to a single modify of the TARGET path.
Audience: Maintainers of the SCV event layer.

## Scenarios

### scv event coalescer/settle (E-04)

#### holds fs events inside the settle window and releases them after it

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Add an fs event at t=0; not ready at t=50 with settle=100; ready at t=150
   - Expected: early.len() equals `0`
   - Expected: scv_coalesce_pending_count(c1) equals `1`
   - Expected: late.len() equals `1`
   - Expected: late[0].path equals `src/a.spl`
   - Expected: scv_coalesce_pending_count(c2) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-EVENT-COALESCE-001
step("Add an fs event at t=0; not ready at t=50 with settle=100; ready at t=150")
var c = scv_coalesce_open(20, 100)
c = scv_coalesce_add(c, _ev(1, "modified", "src/a.spl", ""), "fs", 0)
val (c1, early) = scv_coalesce_flush_ready(c, 50)
expect(early.len()).to_equal(0)
expect(scv_coalesce_pending_count(c1)).to_equal(1)
val (c2, late) = scv_coalesce_flush_ready(c1, 150)
expect(late.len()).to_equal(1)
expect(late[0].path).to_equal("src/a.spl")
expect(scv_coalesce_pending_count(c2)).to_equal(0)
```

</details>

#### micro-batches editor events on the shorter editor window

- Editor events settle after editor_ms (20), before fs settle_ms (100)
   - Expected: early.len() equals `0`
   - Expected: ready.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-EVENT-COALESCE-001
step("Editor events settle after editor_ms (20), before fs settle_ms (100)")
var c = scv_coalesce_open(20, 100)
c = scv_coalesce_add(c, _ev(1, "modified", "src/b.spl", ""), "editor", 0)
val (c1, early) = scv_coalesce_flush_ready(c, 10)
expect(early.len()).to_equal(0)
val (c2, ready) = scv_coalesce_flush_ready(c1, 30)
expect(ready.len()).to_equal(1)
```

</details>

#### flushes save-class events immediately

- A save event is ready at the same tick it was added
   - Expected: now.len() equals `1`
   - Expected: now[0].path equals `src/c.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-EVENT-COALESCE-001
step("A save event is ready at the same tick it was added")
var c = scv_coalesce_open(20, 100)
c = scv_coalesce_add(c, _ev(1, "modified", "src/c.spl", ""), "save", 500)
val (c1, now) = scv_coalesce_flush_ready(c, 500)
expect(now.len()).to_equal(1)
expect(now[0].path).to_equal("src/c.spl")
```

</details>

#### dedupes repeated modifies of one path into a single event

- Three modifies of the same path in one window emit once
   - Expected: out.len() equals `1`
   - Expected: out[0].kind equals `modified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-EVENT-COALESCE-001
step("Three modifies of the same path in one window emit once")
var c = scv_coalesce_open(20, 100)
c = scv_coalesce_add(c, _ev(1, "modified", "src/d.spl", ""), "fs", 0)
c = scv_coalesce_add(c, _ev(2, "modified", "src/d.spl", ""), "fs", 10)
c = scv_coalesce_add(c, _ev(3, "modified", "src/d.spl", ""), "fs", 20)
val (c1, out) = scv_coalesce_flush_ready(c, 200)
expect(out.len()).to_equal(1)
expect(out[0].kind).to_equal("modified")
```

</details>

#### a later event on a path restarts its settle window

- Second modify at t=80 keeps the path unsettled at t=120
   - Expected: mid.len() equals `0`
   - Expected: done.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-EVENT-COALESCE-001
step("Second modify at t=80 keeps the path unsettled at t=120")
var c = scv_coalesce_open(20, 100)
c = scv_coalesce_add(c, _ev(1, "modified", "src/e.spl", ""), "fs", 0)
c = scv_coalesce_add(c, _ev(2, "modified", "src/e.spl", ""), "fs", 80)
val (c1, mid) = scv_coalesce_flush_ready(c, 120)
expect(mid.len()).to_equal(0)
val (c2, done) = scv_coalesce_flush_ready(c1, 181)
expect(done.len()).to_equal(1)
```

</details>

#### defers VCS/bulk events until the bulk generation ends

- Bulk events never settle by time; bulk_end releases them
   - Expected: held.len() equals `0`
   - Expected: released.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-EVENT-COALESCE-001
step("Bulk events never settle by time; bulk_end releases them")
var c = scv_coalesce_open(20, 100)
c = scv_coalesce_bulk_begin(c)
c = scv_coalesce_add(c, _ev(1, "modified", "src/f.spl", ""), "vcs", 0)
c = scv_coalesce_add(c, _ev(2, "created", "src/g.spl", ""), "vcs", 0)
val (c1, held) = scv_coalesce_flush_ready(c, 100000)
expect(held.len()).to_equal(0)
val c2 = scv_coalesce_bulk_end(c1)
val (c3, released) = scv_coalesce_flush_ready(c2, 100001)
expect(released.len()).to_equal(2)
```

</details>

#### coalesces an atomic save (tmp write, rename, tmp delete) to modify-target

- created tmp + renamed target<-tmp + deleted tmp => one modified(target)
   - Expected: out.len() equals `1`
   - Expected: out[0].kind equals `modified`
   - Expected: out[0].path equals `src/h.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-EVENT-COALESCE-001
step("created tmp + renamed target<-tmp + deleted tmp => one modified(target)")
val raw = [_ev(1, "created", "src/h.spl.tmp", ""),
           _ev(2, "renamed", "src/h.spl", "src/h.spl.tmp"),
           _ev(3, "deleted", "src/h.spl.tmp", "")]
val out = scv_coalesce_atomic_save(raw)
expect(out.len()).to_equal(1)
expect(out[0].kind).to_equal("modified")
expect(out[0].path).to_equal("src/h.spl")
```

</details>

#### leaves a genuine rename (no tmp create) untouched by atomic-save folding

- renamed with no matching created stays renamed
   - Expected: out.len() equals `1`
   - Expected: out[0].kind equals `renamed`
   - Expected: out[0].related equals `src/old.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-EVENT-COALESCE-001
step("renamed with no matching created stays renamed")
val raw = [_ev(1, "renamed", "src/new.spl", "src/old.spl")]
val out = scv_coalesce_atomic_save(raw)
expect(out.len()).to_equal(1)
expect(out[0].kind).to_equal("renamed")
expect(out[0].related).to_equal("src/old.spl")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-EVENT-COALESCE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `904b16902beebaa9a75ee13d235422786cda00524d50599df2f753eb39682831`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `904b16902beebaa9a75ee13d235422786cda00524d50599df2f753eb39682831`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `904b16902beebaa9a75ee13d235422786cda00524d50599df2f753eb39682831`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/lib/scv_event_coalesce_spec.spl
mirror: doc/06_spec/integration/lib/scv_event_coalesce_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/integration/lib/scv_event_coalesce_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/lib/scv_event_coalesce_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/lib/scv_event_coalesce_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/lib/scv_event_coalesce_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/lib/scv_event_coalesce_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'holds fs events inside the settle window and releases them after it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/scv_event_coalesce_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'micro-batches editor events on the shorter editor window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/scv_event_coalesce_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flushes save-class events immediately' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
