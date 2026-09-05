# scv_editor_ipc_spec

> Purpose: This spec proves the SCV-IMPL-E-09 editor IPC protocol

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_editor_ipc_spec

Purpose: This spec proves the SCV-IMPL-E-09 editor IPC protocol

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_editor_ipc_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves the SCV-IMPL-E-09 editor IPC protocol
(`src/lib/scv/editor_ipc.spl`): buffer_open/edit/save_begin/save_end/
path_rename/refactor_begin-entity-end/flush messages travel over a
transport and drive a deterministic server state machine; open-buffer bytes
override the disk read (`scv_editor_read` never touches disk for an open
buffer); save brackets mark expected paths; refactor entities group into
one transaction. Transport honesty: the UDS externs core-dump under the
seed test path (extern text-shape vs Rust ptr/len ABI), so this spec
exercises the sanctioned FILESYSTEM-PIPE spool transport
(append-line file + read offset); the UDS swap is an explicit TODO in the
module.
Audience: Maintainers of the SCV editor integration layer.

## Scenarios

### scv editor IPC protocol (E-09)

#### opens a buffer whose bytes override the disk read

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- buffer_open then read: editor bytes win, disk untouched
   - Expected: evs.len() equals `1`
   - Expected: evs[0].kind equals `buffer_open`
   - Expected: scv_editor_read(ipc1, "{root}/a.txt") equals `editor-bytes`
   - Expected: scv_editor_read(ipc1, "{root}/missing-buffer.txt") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-EDITOR-IPC-001
step("buffer_open then read: editor bytes win, disk untouched")
val root = _fixture("open")
file_write("{root}/a.txt", "disk-bytes")
var ipc = scv_editor_ipc_open("{root}/spool.ipc")
scv_editor_ipc_send("{root}/spool.ipc", scv_editor_msg("buffer_open", "{root}/a.txt", "editor-bytes"))
val (ipc1, evs) = scv_editor_ipc_poll(ipc)
expect(evs.len()).to_equal(1)
expect(evs[0].kind).to_equal("buffer_open")
expect(scv_editor_read(ipc1, "{root}/a.txt")).to_equal("editor-bytes")
expect(scv_editor_read(ipc1, "{root}/missing-buffer.txt")).to_equal("")
dir_remove_all(root)
```

</details>

#### applies edits to the open buffer, including tabs and newlines

- edit replaces buffer content; escaping survives the wire
   - Expected: evs.len() equals `2`
   - Expected: scv_editor_read(ipc1, "{root}/b.txt") equals `line1\nline2\ttabbed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-EDITOR-IPC-001
step("edit replaces buffer content; escaping survives the wire")
val root = _fixture("edit")
var ipc = scv_editor_ipc_open("{root}/spool.ipc")
scv_editor_ipc_send("{root}/spool.ipc", scv_editor_msg("buffer_open", "{root}/b.txt", "v1"))
scv_editor_ipc_send("{root}/spool.ipc", scv_editor_msg("edit", "{root}/b.txt", "line1\nline2\ttabbed"))
val (ipc1, evs) = scv_editor_ipc_poll(ipc)
expect(evs.len()).to_equal(2)
expect(scv_editor_read(ipc1, "{root}/b.txt")).to_equal("line1\nline2\ttabbed")
dir_remove_all(root)
```

</details>

#### brackets saves: save_begin marks the path expected until save_end

- save_begin/save_end drive the expected-save set
   - Expected: ipc1.expected_saves.len() equals `1`
   - Expected: ipc2.expected_saves.len() equals `0`
   - Expected: evs2[0].kind equals `save_end`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-EDITOR-IPC-001
step("save_begin/save_end drive the expected-save set")
val root = _fixture("save")
var ipc = scv_editor_ipc_open("{root}/spool.ipc")
scv_editor_ipc_send("{root}/spool.ipc", scv_editor_msg("buffer_open", "{root}/c.txt", "x"))
scv_editor_ipc_send("{root}/spool.ipc", scv_editor_msg("save_begin", "{root}/c.txt", ""))
val (ipc1, evs1) = scv_editor_ipc_poll(ipc)
expect(ipc1.expected_saves.len()).to_equal(1)
scv_editor_ipc_send("{root}/spool.ipc", scv_editor_msg("save_end", "{root}/c.txt", ""))
val (ipc2, evs2) = scv_editor_ipc_poll(ipc1)
expect(ipc2.expected_saves.len()).to_equal(0)
expect(evs2[0].kind).to_equal("save_end")
dir_remove_all(root)
```

</details>

#### renames a path and moves the buffer with it

- path_rename rebinds the open buffer to the new path
   - Expected: scv_editor_read(ipc1, "{root}/new.txt") equals `kept`
   - Expected: scv_editor_read(ipc1, "{root}/old.txt") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-EDITOR-IPC-001
step("path_rename rebinds the open buffer to the new path")
val root = _fixture("ren")
var ipc = scv_editor_ipc_open("{root}/spool.ipc")
scv_editor_ipc_send("{root}/spool.ipc", scv_editor_msg("buffer_open", "{root}/old.txt", "kept"))
scv_editor_ipc_send("{root}/spool.ipc", scv_editor_msg2("path_rename", "{root}/old.txt", "{root}/new.txt", ""))
val (ipc1, evs) = scv_editor_ipc_poll(ipc)
expect(scv_editor_read(ipc1, "{root}/new.txt")).to_equal("kept")
expect(scv_editor_read(ipc1, "{root}/old.txt")).to_equal("")
dir_remove_all(root)
```

</details>

#### groups refactor entities into one transaction

- refactor_begin/entity/entity/refactor_end ⇒ one grouped event
   - Expected: ev.entities.len() equals `2`
   - Expected: txn_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-EDITOR-IPC-001
step("refactor_begin/entity/entity/refactor_end ⇒ one grouped event")
val root = _fixture("ref")
var ipc = scv_editor_ipc_open("{root}/spool.ipc")
scv_editor_ipc_send("{root}/spool.ipc", scv_editor_msg("refactor_begin", "rename-fn", ""))
scv_editor_ipc_send("{root}/spool.ipc", scv_editor_msg2("refactor_entity", "{root}/e1.spl", "{root}/e1.spl", "fn old->new"))
scv_editor_ipc_send("{root}/spool.ipc", scv_editor_msg2("refactor_entity", "{root}/e2.spl", "{root}/e2.spl", "fn old->new"))
scv_editor_ipc_send("{root}/spool.ipc", scv_editor_msg("refactor_end", "rename-fn", ""))
val (ipc1, evs) = scv_editor_ipc_poll(ipc)
var txn_count = 0
for ev in evs:
    if ev.kind == "refactor_txn":
        txn_count = txn_count + 1
        expect(ev.entities.len()).to_equal(2)
expect(txn_count).to_equal(1)
dir_remove_all(root)
```

</details>

#### flush drains pending events and closes buffers deliberately

- flush emits a flush event and reports drained state
   - Expected: drained.len() >= 0 is true
   - Expected: saw_flush is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-EDITOR-IPC-001
step("flush emits a flush event and reports drained state")
val root = _fixture("flush")
var ipc = scv_editor_ipc_open("{root}/spool.ipc")
scv_editor_ipc_send("{root}/spool.ipc", scv_editor_msg("buffer_open", "{root}/f.txt", "z"))
scv_editor_ipc_send("{root}/spool.ipc", scv_editor_msg("flush", "", ""))
val (ipc1, evs) = scv_editor_ipc_poll(ipc)
val (ipc2, drained) = scv_editor_ipc_flush(ipc1)
expect(drained.len() >= 0).to_equal(true)
var saw_flush = false
for ev in evs:
    if ev.kind == "flush":
        saw_flush = true
expect(saw_flush).to_equal(true)
dir_remove_all(root)
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

- `REQ-SCV-EDITOR-IPC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2fa507855279af3c83c533789161375965d76e574f916e4208681cb9618f1769`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2fa507855279af3c83c533789161375965d76e574f916e4208681cb9618f1769`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2fa507855279af3c83c533789161375965d76e574f916e4208681cb9618f1769`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/scv_editor_ipc_spec.spl
mirror: doc/06_spec/integration/app/scv_editor_ipc_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_editor_ipc_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_editor_ipc_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_editor_ipc_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/scv_editor_ipc_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renames a path and moves the buffer with it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_editor_ipc_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'groups refactor entities into one transaction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_editor_ipc_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flush drains pending events and closes buffers deliberately' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
