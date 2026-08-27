# PTY Master/Slave Round-Trip Specification (PTY2)

> Regression coverage for the PTY2 (increment 2) production-harden defect: P4 fixed `tty_write`'s delivery but explicitly deferred the PTY master<->slave round-trip because no endpoint->entity routing layer existed — writing to a master's own `tty_write` only ever reached the master's own OutputBuf, never the linked slave's queue. This spec proves the real routed data path exists in both directions (master plan §10.1):

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# PTY Master/Slave Round-Trip Specification (PTY2)

Regression coverage for the PTY2 (increment 2) production-harden defect: P4 fixed `tty_write`'s delivery but explicitly deferred the PTY master<->slave round-trip because no endpoint->entity routing layer existed — writing to a master's own `tty_write` only ever reached the master's own OutputBuf, never the linked slave's queue. This spec proves the real routed data path exists in both directions (master plan §10.1):

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PTY2-ROUNDTRIP |
| Category | Infrastructure |
| Status | In Progress |
| Source | `test/01_unit/os/tty/pty_roundtrip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Regression coverage for the PTY2 (increment 2) production-harden defect: P4
fixed `tty_write`'s delivery but explicitly deferred the PTY master<->slave
round-trip because no endpoint->entity routing layer existed — writing to a
master's own `tty_write` only ever reached the master's own OutputBuf, never
the linked slave's queue. This spec proves the real routed data path exists
in both directions (master plan §10.1):

- master write -> slave input queue -> shell read
- shell write -> slave output queue -> master read

with exact-byte-content oracles (never just a length check), destructive
drains (a second read must not double-deliver), and a cross-talk negative
oracle proving two independent PTY pairs never leak bytes into each other.

## Scenarios

### TtyService PTY master/slave round-trip

#### master write delivers exact bytes to slave read (shell read)

- master write delivers exact bytes to slave read (shell read)
- PTY master writes 'hello'
- Shell reads from the slave's input queue
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
- A second drain without an intervening write returns empty (consumed)
   - Expected: second.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("master write delivers exact bytes to slave read (shell read)")
var svc = TtyService.new()
val pair = svc.tty_create_pty_pair()
val master = pair.0
val slave  = pair.1

step("PTY master writes 'hello'")
val hello: [u8] = [104, 101, 108, 108, 111]   # "hello"
val accepted = svc.pty_master_write(master, hello)

step("Shell reads from the slave's input queue")
val delivered = svc.tty_read_input(slave)

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

step("A second drain without an intervening write returns empty (consumed)")
val second = svc.tty_read_input(slave)
expect(second.len()).to_equal(0)
```

</details>

#### slave write delivers exact bytes to master read (reverse direction)

- slave write delivers exact bytes to master read (reverse direction)
- Shell (slave side) writes 'world'
- PTY master reads from the slave's output queue
- Assert accepted count equals delivered count
   - Expected: accepted equals `5`
   - Expected: delivered.len() equals `5`
   - Expected: accepted equals `delivered.len()`
- Assert the exact byte content arrived (absolute content oracle)
   - Expected: delivered[0] equals `119)   # 'w'`
   - Expected: delivered[1] equals `111)   # 'o'`
   - Expected: delivered[2] equals `114)   # 'r'`
   - Expected: delivered[3] equals `108)   # 'l'`
   - Expected: delivered[4] equals `100)   # 'd'`
- A second drain without an intervening write returns empty (consumed)
   - Expected: second.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("slave write delivers exact bytes to master read (reverse direction)")
var svc = TtyService.new()
val pair = svc.tty_create_pty_pair()
val master = pair.0
val slave  = pair.1

step("Shell (slave side) writes 'world'")
val world: [u8] = [119, 111, 114, 108, 100]   # "world"
val accepted = svc.pty_slave_write(slave, world)

step("PTY master reads from the slave's output queue")
val delivered = svc.pty_master_read(master)

step("Assert accepted count equals delivered count")
expect(accepted).to_equal(5)
expect(delivered.len()).to_equal(5)
expect(accepted).to_equal(delivered.len())

step("Assert the exact byte content arrived (absolute content oracle)")
expect(delivered[0]).to_equal(119)   # 'w'
expect(delivered[1]).to_equal(111)   # 'o'
expect(delivered[2]).to_equal(114)   # 'r'
expect(delivered[3]).to_equal(108)   # 'l'
expect(delivered[4]).to_equal(100)   # 'd'

step("A second drain without an intervening write returns empty (consumed)")
val second = svc.pty_master_read(master)
expect(second.len()).to_equal(0)
```

</details>

#### cross-talk is impossible between two independent PTY pairs

- cross-talk is impossible between two independent PTY pairs
- Master A writes 'AAAA'; master B writes 'BBBB'
- Slave A's input queue holds only A's bytes
   - Expected: in_a.len() equals `4`
   - Expected: in_a[0] equals `65`
   - Expected: in_a[1] equals `65`
   - Expected: in_a[2] equals `65`
   - Expected: in_a[3] equals `65`
- Slave B's input queue holds only B's bytes — never A's
   - Expected: in_b.len() equals `4`
   - Expected: in_b[0] equals `66`
   - Expected: in_b[1] equals `66`
   - Expected: in_b[2] equals `66`
   - Expected: in_b[3] equals `66`
- Reverse direction: slave A writes 'cccc'; slave B writes 'dddd'
- Master A reads only 'cccc' — never 'dddd'
   - Expected: out_a.len() equals `4`
   - Expected: out_a[0] equals `99`
   - Expected: out_a[1] equals `99`
   - Expected: out_a[2] equals `99`
   - Expected: out_a[3] equals `99`
- Master B reads only 'dddd' — never 'cccc'
   - Expected: out_b.len() equals `4`
   - Expected: out_b[0] equals `100`
   - Expected: out_b[1] equals `100`
   - Expected: out_b[2] equals `100`
   - Expected: out_b[3] equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("cross-talk is impossible between two independent PTY pairs")
var svc = TtyService.new()
val pair_a = svc.tty_create_pty_pair()
val master_a = pair_a.0
val slave_a  = pair_a.1
val pair_b = svc.tty_create_pty_pair()
val master_b = pair_b.0
val slave_b  = pair_b.1

step("Master A writes 'AAAA'; master B writes 'BBBB'")
svc.pty_master_write(master_a, [65, 65, 65, 65])   # "AAAA"
svc.pty_master_write(master_b, [66, 66, 66, 66])   # "BBBB"

step("Slave A's input queue holds only A's bytes")
val in_a = svc.tty_read_input(slave_a)
expect(in_a.len()).to_equal(4)
expect(in_a[0]).to_equal(65)
expect(in_a[1]).to_equal(65)
expect(in_a[2]).to_equal(65)
expect(in_a[3]).to_equal(65)

step("Slave B's input queue holds only B's bytes — never A's")
val in_b = svc.tty_read_input(slave_b)
expect(in_b.len()).to_equal(4)
expect(in_b[0]).to_equal(66)
expect(in_b[1]).to_equal(66)
expect(in_b[2]).to_equal(66)
expect(in_b[3]).to_equal(66)

step("Reverse direction: slave A writes 'cccc'; slave B writes 'dddd'")
svc.pty_slave_write(slave_a, [99, 99, 99, 99])     # "cccc"
svc.pty_slave_write(slave_b, [100, 100, 100, 100]) # "dddd"

step("Master A reads only 'cccc' — never 'dddd'")
val out_a = svc.pty_master_read(master_a)
expect(out_a.len()).to_equal(4)
expect(out_a[0]).to_equal(99)
expect(out_a[1]).to_equal(99)
expect(out_a[2]).to_equal(99)
expect(out_a[3]).to_equal(99)

step("Master B reads only 'dddd' — never 'cccc'")
val out_b = svc.pty_master_read(master_b)
expect(out_b.len()).to_equal(4)
expect(out_b[0]).to_equal(100)
expect(out_b[1]).to_equal(100)
expect(out_b[2]).to_equal(100)
expect(out_b[3]).to_equal(100)
```

</details>

#### pty_master_write returns -1 for an entity that is not a PTY master

- pty_master_write returns -1 for an entity that is not a PTY master
   - Expected: rc equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("pty_master_write returns -1 for an entity that is not a PTY master")
var svc = TtyService.new()
val plain = svc.tty_create(TTY_CONSOLE, 1, 2)
val rc = svc.pty_master_write(plain, [1, 2, 3])
expect(rc).to_equal(-1)
```

</details>

#### pty_master_read returns empty for an entity that is not a PTY master

- pty_master_read returns empty for an entity that is not a PTY master
   - Expected: out.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("pty_master_read returns empty for an entity that is not a PTY master")
var svc = TtyService.new()
val plain = svc.tty_create(TTY_CONSOLE, 1, 2)
val out = svc.pty_master_read(plain)
expect(out.len()).to_equal(0)
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

- `REQ-SSPEC-UNIT`
- `REQ-PTY2-001`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `25d69da425bd974e5d622efc7009d37c88a86e68ee0d6339dc7cc6ff242f97b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `25d69da425bd974e5d622efc7009d37c88a86e68ee0d6339dc7cc6ff242f97b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `25d69da425bd974e5d622efc7009d37c88a86e68ee0d6339dc7cc6ff242f97b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/tty/pty_roundtrip_spec.spl
mirror: doc/06_spec/01_unit/os/tty/pty_roundtrip_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/os/tty/pty_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/tty/pty_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/tty/pty_roundtrip_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 28 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/tty/pty_roundtrip_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/tty/pty_roundtrip_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'master write delivers exact bytes to slave read (shell read)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tty/pty_roundtrip_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'slave write delivers exact bytes to master read (reverse direction)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tty/pty_roundtrip_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cross-talk is impossible between two independent PTY pairs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
