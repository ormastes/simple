# Parent Commit Piped Process Specification

> Tests covering ParentCommitPipedResultReaderV1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parent Commit Piped Process Specification

## Scenarios

### ParentCommitPipedResultReaderV1

#### rejects a child session whose generation does not match its inbox

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects a child session whose generation does not match its inbox


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a child session whose generation does not match its inbox")
val inbox = parent_commit_frame_inbox_v1_for_generation(1, 41)
val session = parent_commit_piped_process_session_v1(
    "/bin/echo", ["unused"], 42, inbox)
assert_equal(session.status().process_handle, -1)
assert_equal(session.status().terminal_reason,
    "generation-binding-mismatch")
assert_false(session.close())
assert_equal(session.status().close_attempts, 0)
```

</details>

#### rejects the reserved zero generation

- rejects the reserved zero generation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the reserved zero generation")
val inbox = parent_commit_frame_inbox_v1_for_generation(1, 0)
val session = parent_commit_piped_process_session_v1(
    "/bin/echo", ["unused"], 0, inbox)
assert_equal(session.status().process_handle, -1)
assert_equal(session.status().terminal_reason,
    "generation-binding-mismatch")
```

</details>

#### reassembles a child result split across stdout reads

- reassembles a child result split across stdout reads


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reassembles a child result split across stdout reads")
val inbox = parent_commit_frame_inbox_v1(2)
val reader = parent_commit_piped_result_reader_v1(inbox)
val line = piped_child_line(7, 707)
val split = line.len() / 2
val first = reader.receive_stdout_chunk(line.substring(0, split), 2)
assert_true(first.ok)
assert_equal(first.accepted, 0)
assert_true(first.pending_bytes > 0)
val second = reader.receive_stdout_chunk(line.substring(split, line.len()), 2)
assert_true(second.ok)
assert_equal(second.accepted, 1)
assert_equal(second.rejected, 0)
assert_equal(reader.pending_byte_count(), 0)
assert_true(reader.pending_high_water_byte_count() > 0)
assert_true(reader.pending_high_water_byte_count() < line.len())
val received = inbox.receive()
assert_true(received.ok)
assert_equal(received.frame, piped_child_frame(7, 707))
```

</details>

#### keeps complete later lines pending at the parent scheduling budget

- keeps complete later lines pending at the parent scheduling budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps complete later lines pending at the parent scheduling budget")
val inbox = parent_commit_frame_inbox_v1(3)
val reader = parent_commit_piped_result_reader_v1(inbox)
val first = piped_child_line(1, 701)
val second = piped_child_line(2, 702)
val one = reader.receive_stdout_chunk(first + second, 1)
assert_true(one.ok)
assert_equal(one.accepted, 1)
assert_true(one.pending_bytes > 0)
val two = reader.receive_stdout_chunk("", 1)
assert_true(two.ok)
assert_equal(two.accepted, 1)
assert_equal(reader.pending_high_water_byte_count(), second.len())
assert_equal(inbox.receive().frame, piped_child_frame(1, 701))
assert_equal(inbox.receive().frame, piped_child_frame(2, 702))
```

</details>

#### rejects bad and oversized stdout without retaining it

- rejects bad and oversized stdout without retaining it


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects bad and oversized stdout without retaining it")
val inbox = parent_commit_frame_inbox_v1(1)
val reader = parent_commit_piped_result_reader_v1_with_line_budget(inbox, 8)
val invalid = reader.receive_stdout_chunk("unexpected output\n", 1)
assert_true(invalid.ok)
assert_equal(invalid.accepted, 0)
assert_equal(invalid.rejected, 1)
val oversized = "012345678\n"
val rejected = reader.receive_stdout_chunk(oversized, 1)
assert_true(rejected.ok)
assert_true(rejected.rejected >= 1)
assert_equal(reader.pending_byte_count(), 0)
assert_equal(reader.pending_high_water_byte_count(), 8)
val non_ascii = reader.receive_stdout_chunk("é\n", 1)
assert_equal(non_ascii.ok, false)
assert_equal(non_ascii.reason, "non-ascii-stdout")
assert_equal(non_ascii.pending_bytes, 0)
assert_equal(reader.pending_byte_count(), 0)
```

</details>

#### closes the shared inbox and rejects invalid process handles

- closes the shared inbox and rejects invalid process handles


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closes the shared inbox and rejects invalid process handles")
val inbox = parent_commit_frame_inbox_v1(1)
val reader = parent_commit_piped_result_reader_v1(inbox)
assert_equal(reader.poll_process_stdout(0, 1).reason, "invalid-process-handle")
reader.close()
assert_true(reader.is_closed())
assert_true(inbox.is_closed())
assert_false(inbox.offer_process_result_frame(piped_child_frame(1, 701)))
val after_close = reader.receive_stdout_chunk(piped_child_line(1, 701), 1)
assert_equal(after_close.ok, false)
assert_equal(after_close.reason, "reader-closed")
assert_equal(after_close.pending_bytes, 0)
assert_equal(reader.pending_byte_count(), 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/parent_commit_piped_process_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ParentCommitPipedResultReaderV1.
- ParentCommitPipedResultReaderV1

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0f34018bd406845fbc6c1883dd9d350e8416ec7f568ee5925e53b1d67a364a6d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0f34018bd406845fbc6c1883dd9d350e8416ec7f568ee5925e53b1d67a364a6d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0f34018bd406845fbc6c1883dd9d350e8416ec7f568ee5925e53b1d67a364a6d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/parent_commit_piped_process_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/parent_commit_piped_process_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/parent_commit_piped_process_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/parent_commit_piped_process_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/parent_commit_piped_process_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a child session whose generation does not match its inbox' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/parent_commit_piped_process_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects the reserved zero generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/parent_commit_piped_process_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reassembles a child result split across stdout reads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
