# TTY Write Delivery Specification (P4)

> Regression coverage for the P4 (Services/TTY) production-harden defect: `tty_write()` previously returned an "accepted" byte count without ever delivering the bytes anywhere — a subsequent read of the output path saw nothing. This spec proves real delivery: bytes written through `tty_write` must be observable by draining the TTY's output queue via `tty_read_output`, with an exact-byte oracle (not just a count check).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TTY Write Delivery Specification (P4)

Regression coverage for the P4 (Services/TTY) production-harden defect: `tty_write()` previously returned an "accepted" byte count without ever delivering the bytes anywhere — a subsequent read of the output path saw nothing. This spec proves real delivery: bytes written through `tty_write` must be observable by draining the TTY's output queue via `tty_read_output`, with an exact-byte oracle (not just a count check).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #P4-TTY |
| Category | Infrastructure |
| Status | In Progress |
| Source | `test/01_unit/os/tty/tty_write_delivery_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Regression coverage for the P4 (Services/TTY) production-harden defect:
`tty_write()` previously returned an "accepted" byte count without ever
delivering the bytes anywhere — a subsequent read of the output path saw
nothing. This spec proves real delivery: bytes written through `tty_write`
must be observable by draining the TTY's output queue via
`tty_read_output`, with an exact-byte oracle (not just a count check).

## Key Concepts

| Concept          | Description |
|-------------------|-------------|
| OutputBuf         | Per-entity output byte queue tty_write appends to |
| tty_read_output   | Drains OutputBuf; the "subsequent read" side of the path |
| Accepted==Delivered | The count tty_write returns must equal what actually arrives |

## Behavior

- tty_write("hello") followed by tty_read_output returns the exact bytes "hello"
- The count tty_write returns equals the number of bytes tty_read_output delivers
- Draining is destructive: a second read after a drain returns nothing new
- Multiple writes accumulate in order before a drain
- A PTY master-write -> slave-read round-trip is NOT YET wired (no
  endpoint->entity routing exists in TtyService); this is recorded as the
  next increment in .spipe/simpleos_harden_p4_tty/state.md, not silently
  skipped.

## Scenarios

### TtyService tty_write real delivery

#### delivers the exact bytes written through tty_write to tty_read_output

- delivers the exact bytes written through tty_write to tty_read_output
- Write 'hello' through tty_write
- Read the delivered bytes from the output queue
- Assert accepted count equals delivered count
   - Expected: accepted equals `5`
   - Expected: delivered.len() equals `5`
   - Expected: accepted equals `delivered.len()`
- Assert the exact byte content arrived (absolute content oracle)
   - Expected: delivered[0] equals `104)   # 'h'`
   - Expected: delivered[1] equals `101)   # 'e'`
   - Expected: delivered[2] equals `108)   # 'l'`
   - Expected: delivered[3] equals `108)   # 'l'`
   - Expected: delivered[4] equals `111)   # 'o'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("delivers the exact bytes written through tty_write to tty_read_output")
var svc = TtyService.new()
val tty = svc.tty_create(TTY_CONSOLE, 1, 2)

step("Write 'hello' through tty_write")
val hello: [u8] = [104, 101, 108, 108, 111]   # "hello"
val accepted = svc.tty_write(tty, hello)

step("Read the delivered bytes from the output queue")
val delivered = svc.tty_read_output(tty)

step("Assert accepted count equals delivered count")
expect(accepted).to_equal(5)
expect(delivered.len()).to_equal(5)
expect(accepted).to_equal(delivered.len())

step("Assert the exact byte content arrived (absolute content oracle)")
expect(delivered[0]).to_equal(104)   # 'h'
expect(delivered[1]).to_equal(101)   # 'e'
expect(delivered[2]).to_equal(108)   # 'l'
expect(delivered[3]).to_equal(108)   # 'l'
expect(delivered[4]).to_equal(111)   # 'o'
```

</details>

#### drains destructively — a second read sees nothing new

- drains destructively — a second read sees nothing new
- Write once, drain once
   - Expected: first.len() equals `2`
- Read again without an intervening write
   - Expected: second.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("drains destructively — a second read sees nothing new")
var svc = TtyService.new()
val tty = svc.tty_create(TTY_CONSOLE, 1, 2)
val data: [u8] = [65, 66]   # "AB"

step("Write once, drain once")
svc.tty_write(tty, data)
val first = svc.tty_read_output(tty)
expect(first.len()).to_equal(2)

step("Read again without an intervening write")
val second = svc.tty_read_output(tty)
expect(second.len()).to_equal(0)
```

</details>

#### accumulates bytes across multiple writes in order before a drain

- accumulates bytes across multiple writes in order before a drain
- Write 'ab' then 'cd' without draining in between
- Drain once and assert the full ordered sequence
   - Expected: all.len() equals `4`
   - Expected: all[0] equals `97`
   - Expected: all[1] equals `98`
   - Expected: all[2] equals `99`
   - Expected: all[3] equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accumulates bytes across multiple writes in order before a drain")
var svc = TtyService.new()
val tty = svc.tty_create(TTY_CONSOLE, 1, 2)

step("Write 'ab' then 'cd' without draining in between")
svc.tty_write(tty, [97, 98])   # "ab"
svc.tty_write(tty, [99, 100])  # "cd"

step("Drain once and assert the full ordered sequence")
val all = svc.tty_read_output(tty)
expect(all.len()).to_equal(4)
expect(all[0]).to_equal(97)
expect(all[1]).to_equal(98)
expect(all[2]).to_equal(99)
expect(all[3]).to_equal(100)
```

</details>

#### tty_read_output returns empty for an unknown entity

- tty_read_output returns empty for an unknown entity
   - Expected: out.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("tty_read_output returns empty for an unknown entity")
var svc = TtyService.new()
val ghost = Entity(id: 9999, generation: 1)
val out = svc.tty_read_output(ghost)
expect(out.len()).to_equal(0)
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

- `REQ-SSPEC-UNIT`
- `REQ-P4-TTY-001`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eca6fcc77df378f21ffda22d2e6045b21645c23c80d3ca0e1d14cb50e24dc2fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eca6fcc77df378f21ffda22d2e6045b21645c23c80d3ca0e1d14cb50e24dc2fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eca6fcc77df378f21ffda22d2e6045b21645c23c80d3ca0e1d14cb50e24dc2fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/tty/tty_write_delivery_spec.spl
mirror: doc/06_spec/01_unit/os/tty/tty_write_delivery_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/os/tty/tty_write_delivery_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/tty/tty_write_delivery_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/tty/tty_write_delivery_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/tty/tty_write_delivery_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/tty/tty_write_delivery_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'delivers the exact bytes written through tty_write to tty_read_output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tty/tty_write_delivery_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'drains destructively — a second read sees nothing new' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tty/tty_write_delivery_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accumulates bytes across multiple writes in order before a drain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
