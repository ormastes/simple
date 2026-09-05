# scv_event_journal_spec

> Purpose: This spec proves SCV-IMPL-E-03 event journal integration: watcher

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_event_journal_spec

Purpose: This spec proves SCV-IMPL-E-03 event journal integration: watcher

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_event_journal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV-IMPL-E-03 event journal integration: watcher
event batches land as pending files under `.scv/journal/event_batches/`,
commit appends framed `kind=fsevent` lines (op = batch id) to the MIG-10
append-only events.log with a durable committed marker, and replay is
idempotent — a second replay commits nothing and leaves events.log
byte-identical. The `scv event-record|event-commit|event-replay|events` CLI
drives the same disk state.
Audience: Maintainers of the SCV storage/event layers.

## Scenarios

### scv event journal integration (E-03)

#### records events into a pending, uncommitted batch

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records events into a pending, uncommitted batch
- Record two events; pending file exists, batch not committed
   - Expected: scv_event_batch_record(root, "b1", "created", "a.txt", "") is true
   - Expected: scv_event_batch_record(root, "b1", "modified", "a.txt", "") is true
   - Expected: file_exists(scv_event_batch_pending_path(root, "b1")) is true
   - Expected: scv_event_batch_is_committed(root, "b1") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("records events into a pending, uncommitted batch")
step("Record two events; pending file exists, batch not committed")
val root = _repo("pending")
expect(scv_event_batch_record(root, "b1", "created", "a.txt", "")).to_equal(true)
expect(scv_event_batch_record(root, "b1", "modified", "a.txt", "")).to_equal(true)
expect(file_exists(scv_event_batch_pending_path(root, "b1"))).to_equal(true)
expect(scv_event_batch_is_committed(root, "b1")).to_equal(false)
dir_remove_all(root)
```

</details>

#### commits a batch into the append-only events.log exactly once

- commits a batch into the append-only events.log exactly once
- Commit, verify framed lines + marker; a second commit adds nothing
   - Expected: scv_event_batch_commit(root, "b1") is true
   - Expected: after - before equals `2`
   - Expected: scv_event_batch_is_committed(root, "b1") is true
   - Expected: file_exists(scv_event_batch_pending_path(root, "b1")) is false
   - Expected: scv_event_batch_commit(root, "b1") is true
   - Expected: _events_lines(root) equals `after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("commits a batch into the append-only events.log exactly once")
step("Commit, verify framed lines + marker; a second commit adds nothing")
val root = _repo("commit")
scv_event_batch_record(root, "b1", "created", "a.txt", "")
scv_event_batch_record(root, "b1", "deleted", "b.txt", "")
val before = _events_lines(root)
expect(scv_event_batch_commit(root, "b1")).to_equal(true)
val after = _events_lines(root)
expect(after - before).to_equal(2)
expect(scv_event_batch_is_committed(root, "b1")).to_equal(true)
expect(file_exists(scv_event_batch_pending_path(root, "b1"))).to_equal(false)
val log = file_read(scv_journal_events_path(root))
expect(log).to_contain("op=b1 kind=fsevent")
expect(scv_event_batch_commit(root, "b1")).to_equal(true)
expect(_events_lines(root)).to_equal(after)
dir_remove_all(root)
```

</details>

#### replays pending batches idempotently

- replays pending batches idempotently
- Replay commits both batches; a second replay commits zero
   - Expected: scv_event_batch_replay(root) equals `2`
   - Expected: scv_event_batch_replay(root) equals `0`
   - Expected: _events_lines(root) equals `lines`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("replays pending batches idempotently")
step("Replay commits both batches; a second replay commits zero")
val root = _repo("replay")
scv_event_batch_record(root, "b1", "created", "a.txt", "")
scv_event_batch_record(root, "b2", "created", "b.txt", "")
expect(scv_event_batch_replay(root)).to_equal(2)
val lines = _events_lines(root)
expect(scv_event_batch_replay(root)).to_equal(0)
expect(_events_lines(root)).to_equal(lines)
expect(scv_event_log(root)).to_contain("op=b2 kind=fsevent")
dir_remove_all(root)
```

</details>

#### drives the same lifecycle through the scv CLI dispatch

- drives the same lifecycle through the scv CLI dispatch
- scv event-record / event-commit / events over a real repo


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("drives the same lifecycle through the scv CLI dispatch")
step("scv event-record / event-commit / events over a real repo")
val script = [
    "set -eu",
    "REPO=$(pwd)",
    "TMP=$(mktemp -d /tmp/scv-event-cli.XXXXXX)",
    "scv() { SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" \"$@\"; }",
    "cd \"$TMP\"",
    "scv init >/dev/null",
    "scv event-record cli1 created a.txt",
    "scv event-commit cli1",
    "scv event-replay",
    "scv events",
    "printf 'cli=done\\n'"
].join("\n") + "\n"
val (out, err, code) = process_run("/bin/sh", ["-c", script])
val combined = "{out}{err}\nexit={code}\n"
expect(combined).to_contain("recorded batch=cli1")
expect(combined).to_contain("committed batch=cli1")
expect(combined).to_contain("op=cli1 kind=fsevent")
expect(combined).to_contain("cli=done")
expect(combined).to_contain("exit=0")
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

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-EVENT-JOURNAL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `efe866051a9c72a32936950441b5f359849df62ba58a99793cd82f8a447afe8d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `efe866051a9c72a32936950441b5f359849df62ba58a99793cd82f8a447afe8d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `efe866051a9c72a32936950441b5f359849df62ba58a99793cd82f8a447afe8d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_event_journal_spec.spl
mirror: doc/06_spec/integration/app/scv_event_journal_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/integration/app/scv_event_journal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_event_journal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_event_journal_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/scv_event_journal_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_event_journal_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records events into a pending, uncommitted batch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_event_journal_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'commits a batch into the append-only events.log exactly once' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_event_journal_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replays pending batches idempotently' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
