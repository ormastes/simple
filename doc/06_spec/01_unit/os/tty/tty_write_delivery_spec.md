# TTY Write Delivery Specification (P4)

> Verifies the tty write delivery behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TTY Write Delivery Specification (P4)

Verifies the tty write delivery behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #P4-TTY |
| Category | Infrastructure |
| Status | In Progress |
| Source | `test/01_unit/os/tty/tty_write_delivery_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the tty write delivery behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### TtyService tty_write real delivery

#### delivers the exact bytes written through tty_write to tty_read_output

- Verify: delivers the exact bytes written through tty_write to tty_read_output
- Write 'hello' through tty_write
- Read the delivered bytes from the output queue
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


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-P4-TTY-001
step("Verify: delivers the exact bytes written through tty_write to tty_read_output")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var svc = TtyService.new()
val tty = svc.tty_create(TTY_CONSOLE, 1, 2)

step("Write 'hello' through tty_write")
val hello: [u8] = [104, 101, 108, 108, 111]   # "hello"
val accepted = svc.tty_write(tty, hello)

step("Read the delivered bytes from the output queue")
val delivered = svc.tty_read_output(tty)

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
```

</details>

#### drains destructively — a second read sees nothing new

- Verify: drains destructively — a second read sees nothing new
- Write once, drain once
   - Expected: first.len() equals `2)  # oracle: pinned constant asserted by this scenario`
- Read again without an intervening write
   - Expected: second.len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-P4-TTY-001
step("Verify: drains destructively — a second read sees nothing new")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var svc = TtyService.new()
val tty = svc.tty_create(TTY_CONSOLE, 1, 2)
val data: [u8] = [65, 66]   # "AB"

step("Write once, drain once")
svc.tty_write(tty, data)
val first = svc.tty_read_output(tty)
expect(first.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario

step("Read again without an intervening write")
val second = svc.tty_read_output(tty)
expect(second.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### accumulates bytes across multiple writes in order before a drain

- Verify: accumulates bytes across multiple writes in order before a drain
- Write 'ab' then 'cd' without draining in between
- Drain once and assert the full ordered sequence
   - Expected: all.len() equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: all[0] equals `97)  # oracle: pinned constant asserted by this scenario`
   - Expected: all[1] equals `98)  # oracle: pinned constant asserted by this scenario`
   - Expected: all[2] equals `99)  # oracle: pinned constant asserted by this scenario`
   - Expected: all[3] equals `100)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-P4-TTY-001
step("Verify: accumulates bytes across multiple writes in order before a drain")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var svc = TtyService.new()
val tty = svc.tty_create(TTY_CONSOLE, 1, 2)

step("Write 'ab' then 'cd' without draining in between")
svc.tty_write(tty, [97, 98])   # "ab"
svc.tty_write(tty, [99, 100])  # "cd"

step("Drain once and assert the full ordered sequence")
val all = svc.tty_read_output(tty)
expect(all.len()).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect(all[0]).to_equal(97)  # oracle: pinned constant asserted by this scenario
expect(all[1]).to_equal(98)  # oracle: pinned constant asserted by this scenario
expect(all[2]).to_equal(99)  # oracle: pinned constant asserted by this scenario
expect(all[3]).to_equal(100)  # oracle: pinned constant asserted by this scenario
```

</details>

#### tty_read_output returns empty for an unknown entity

- Verify: tty_read_output returns empty for an unknown entity
   - Expected: out.len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-P4-TTY-001
step("Verify: tty_read_output returns empty for an unknown entity")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var svc = TtyService.new()
val ghost = Entity(id: 9999, generation: 1)
val out = svc.tty_read_output(ghost)
expect(out.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `de1354667469c512184d1c22e72805539ca38195e1ab5cdd68add7d63e93f97f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `de1354667469c512184d1c22e72805539ca38195e1ab5cdd68add7d63e93f97f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `de1354667469c512184d1c22e72805539ca38195e1ab5cdd68add7d63e93f97f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/tty/tty_write_delivery_spec.spl
mirror: doc/06_spec/01_unit/os/tty/tty_write_delivery_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/tty/tty_write_delivery_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/tty/tty_write_delivery_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/tty/tty_write_delivery_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
