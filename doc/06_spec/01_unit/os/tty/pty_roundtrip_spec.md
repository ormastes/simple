# PTY Master/Slave Round-Trip Specification (PTY2)

> Verifies the pty roundtrip behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# PTY Master/Slave Round-Trip Specification (PTY2)

Verifies the pty roundtrip behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PTY2-ROUNDTRIP |
| Category | Infrastructure |
| Status | In Progress |
| Source | `test/01_unit/os/tty/pty_roundtrip_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the pty roundtrip behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### TtyService PTY master/slave round-trip

#### master write delivers exact bytes to slave read (shell read)

- Verify: master write delivers exact bytes to slave read (shell read)
- PTY master writes 'hello'
- Shell reads from the slave's input queue
- Assert accepted count equals delivered count
   - Expected: accepted equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: delivered.len() equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: accepted equals `delivered.len()`
- Assert the exact byte content arrived (absolute content oracle)
   - Expected: delivered[0] equals `104)   # 'h'  # oracle: pinned constant asserted by this scenario`
   - Expected: delivered[1] equals `101)   # 'e'  # oracle: pinned constant asserted by this scenario`
   - Expected: delivered[2] equals `108)   # 'l'  # oracle: pinned constant asserted by this scenario`
   - Expected: delivered[3] equals `108)   # 'l'  # oracle: pinned constant asserted by this scenario`
   - Expected: delivered[4] equals `111)   # 'o'  # oracle: pinned constant asserted by this scenario`
- A second drain without an intervening write returns empty (consumed)
   - Expected: second.len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-PTY2-001
step("Verify: master write delivers exact bytes to slave read (shell read)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
expect(accepted).to_equal(5)  # oracle: pinned constant asserted by this scenario
expect(delivered.len()).to_equal(5)  # oracle: pinned constant asserted by this scenario
expect(accepted).to_equal(delivered.len())

step("Assert the exact byte content arrived (absolute content oracle)")
expect(delivered[0]).to_equal(104)   # 'h'  # oracle: pinned constant asserted by this scenario
expect(delivered[1]).to_equal(101)   # 'e'  # oracle: pinned constant asserted by this scenario
expect(delivered[2]).to_equal(108)   # 'l'  # oracle: pinned constant asserted by this scenario
expect(delivered[3]).to_equal(108)   # 'l'  # oracle: pinned constant asserted by this scenario
expect(delivered[4]).to_equal(111)   # 'o'  # oracle: pinned constant asserted by this scenario

step("A second drain without an intervening write returns empty (consumed)")
val second = svc.tty_read_input(slave)
expect(second.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### slave write delivers exact bytes to master read (reverse direction)

- Verify: slave write delivers exact bytes to master read (reverse direction)
- Shell (slave side) writes 'world'
- PTY master reads from the slave's output queue
- Assert accepted count equals delivered count
   - Expected: accepted equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: delivered.len() equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: accepted equals `delivered.len()`
- Assert the exact byte content arrived (absolute content oracle)
   - Expected: delivered[0] equals `119)   # 'w'  # oracle: pinned constant asserted by this scenario`
   - Expected: delivered[1] equals `111)   # 'o'  # oracle: pinned constant asserted by this scenario`
   - Expected: delivered[2] equals `114)   # 'r'  # oracle: pinned constant asserted by this scenario`
   - Expected: delivered[3] equals `108)   # 'l'  # oracle: pinned constant asserted by this scenario`
   - Expected: delivered[4] equals `100)   # 'd'  # oracle: pinned constant asserted by this scenario`
- A second drain without an intervening write returns empty (consumed)
   - Expected: second.len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-PTY2-001
step("Verify: slave write delivers exact bytes to master read (reverse direction)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
expect(accepted).to_equal(5)  # oracle: pinned constant asserted by this scenario
expect(delivered.len()).to_equal(5)  # oracle: pinned constant asserted by this scenario
expect(accepted).to_equal(delivered.len())

step("Assert the exact byte content arrived (absolute content oracle)")
expect(delivered[0]).to_equal(119)   # 'w'  # oracle: pinned constant asserted by this scenario
expect(delivered[1]).to_equal(111)   # 'o'  # oracle: pinned constant asserted by this scenario
expect(delivered[2]).to_equal(114)   # 'r'  # oracle: pinned constant asserted by this scenario
expect(delivered[3]).to_equal(108)   # 'l'  # oracle: pinned constant asserted by this scenario
expect(delivered[4]).to_equal(100)   # 'd'  # oracle: pinned constant asserted by this scenario

step("A second drain without an intervening write returns empty (consumed)")
val second = svc.pty_master_read(master)
expect(second.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### cross-talk is impossible between two independent PTY pairs

- Verify: cross-talk is impossible between two independent PTY pairs
- Master A writes 'AAAA'; master B writes 'BBBB'
- Slave A's input queue holds only A's bytes
   - Expected: in_a.len() equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: in_a[0] equals `65)  # oracle: pinned constant asserted by this scenario`
   - Expected: in_a[1] equals `65)  # oracle: pinned constant asserted by this scenario`
   - Expected: in_a[2] equals `65)  # oracle: pinned constant asserted by this scenario`
   - Expected: in_a[3] equals `65)  # oracle: pinned constant asserted by this scenario`
- Slave B's input queue holds only B's bytes — never A's
   - Expected: in_b.len() equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: in_b[0] equals `66)  # oracle: pinned constant asserted by this scenario`
   - Expected: in_b[1] equals `66)  # oracle: pinned constant asserted by this scenario`
   - Expected: in_b[2] equals `66)  # oracle: pinned constant asserted by this scenario`
   - Expected: in_b[3] equals `66)  # oracle: pinned constant asserted by this scenario`
- Reverse direction: slave A writes 'cccc'; slave B writes 'dddd'
- Master A reads only 'cccc' — never 'dddd'
   - Expected: out_a.len() equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: out_a[0] equals `99)  # oracle: pinned constant asserted by this scenario`
   - Expected: out_a[1] equals `99)  # oracle: pinned constant asserted by this scenario`
   - Expected: out_a[2] equals `99)  # oracle: pinned constant asserted by this scenario`
   - Expected: out_a[3] equals `99)  # oracle: pinned constant asserted by this scenario`
- Master B reads only 'dddd' — never 'cccc'
   - Expected: out_b.len() equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: out_b[0] equals `100)  # oracle: pinned constant asserted by this scenario`
   - Expected: out_b[1] equals `100)  # oracle: pinned constant asserted by this scenario`
   - Expected: out_b[2] equals `100)  # oracle: pinned constant asserted by this scenario`
   - Expected: out_b[3] equals `100)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-PTY2-001
step("Verify: cross-talk is impossible between two independent PTY pairs")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
expect(in_a.len()).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect(in_a[0]).to_equal(65)  # oracle: pinned constant asserted by this scenario
expect(in_a[1]).to_equal(65)  # oracle: pinned constant asserted by this scenario
expect(in_a[2]).to_equal(65)  # oracle: pinned constant asserted by this scenario
expect(in_a[3]).to_equal(65)  # oracle: pinned constant asserted by this scenario

step("Slave B's input queue holds only B's bytes — never A's")
val in_b = svc.tty_read_input(slave_b)
expect(in_b.len()).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect(in_b[0]).to_equal(66)  # oracle: pinned constant asserted by this scenario
expect(in_b[1]).to_equal(66)  # oracle: pinned constant asserted by this scenario
expect(in_b[2]).to_equal(66)  # oracle: pinned constant asserted by this scenario
expect(in_b[3]).to_equal(66)  # oracle: pinned constant asserted by this scenario

step("Reverse direction: slave A writes 'cccc'; slave B writes 'dddd'")
svc.pty_slave_write(slave_a, [99, 99, 99, 99])     # "cccc"
svc.pty_slave_write(slave_b, [100, 100, 100, 100]) # "dddd"

step("Master A reads only 'cccc' — never 'dddd'")
val out_a = svc.pty_master_read(master_a)
expect(out_a.len()).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect(out_a[0]).to_equal(99)  # oracle: pinned constant asserted by this scenario
expect(out_a[1]).to_equal(99)  # oracle: pinned constant asserted by this scenario
expect(out_a[2]).to_equal(99)  # oracle: pinned constant asserted by this scenario
expect(out_a[3]).to_equal(99)  # oracle: pinned constant asserted by this scenario

step("Master B reads only 'dddd' — never 'cccc'")
val out_b = svc.pty_master_read(master_b)
expect(out_b.len()).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect(out_b[0]).to_equal(100)  # oracle: pinned constant asserted by this scenario
expect(out_b[1]).to_equal(100)  # oracle: pinned constant asserted by this scenario
expect(out_b[2]).to_equal(100)  # oracle: pinned constant asserted by this scenario
expect(out_b[3]).to_equal(100)  # oracle: pinned constant asserted by this scenario
```

</details>

#### pty_master_write returns -1 for an entity that is not a PTY master

- Verify: pty_master_write returns -1 for an entity that is not a PTY master
   - Expected: rc equals `-1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-PTY2-001
step("Verify: pty_master_write returns -1 for an entity that is not a PTY master")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var svc = TtyService.new()
val plain = svc.tty_create(TTY_CONSOLE, 1, 2)
val rc = svc.pty_master_write(plain, [1, 2, 3])
expect(rc).to_equal(-1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### pty_master_read returns empty for an entity that is not a PTY master

- Verify: pty_master_read returns empty for an entity that is not a PTY master
   - Expected: out.len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-PTY2-001
step("Verify: pty_master_read returns empty for an entity that is not a PTY master")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var svc = TtyService.new()
val plain = svc.tty_create(TTY_CONSOLE, 1, 2)
val out = svc.pty_master_read(plain)
expect(out.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `660d946c6888dc543590d4312b38be7363631f677362544d6f4663e81f04341a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `660d946c6888dc543590d4312b38be7363631f677362544d6f4663e81f04341a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `660d946c6888dc543590d4312b38be7363631f677362544d6f4663e81f04341a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/tty/pty_roundtrip_spec.spl
mirror: doc/06_spec/01_unit/os/tty/pty_roundtrip_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/tty/pty_roundtrip_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/tty/pty_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/tty/pty_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
