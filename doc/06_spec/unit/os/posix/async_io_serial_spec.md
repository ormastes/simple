# Async I/O Serial Read Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async I/O Serial Read Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #B4 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/unit/os/posix/async_io_serial_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### async_io serial read

#### serial read request transitions ASYNC_PENDING to ASYNC_COMPLETE

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- serial read request transitions ASYNC_PENDING to ASYNC_COMPLETE
   - Expected: req.state equals `ASYNC_COMPLETE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serial read request transitions ASYNC_PENDING to ASYNC_COMPLETE")
val req = simulate_serial_read(FD_TYPE_SERIAL)
expect(req.state).to_equal(ASYNC_COMPLETE)
```

</details>

#### serial read result is 1 byte

- serial read result is 1 byte
   - Expected: req.result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serial read result is 1 byte")
val req = simulate_serial_read(FD_TYPE_SERIAL)
expect(req.result).to_equal(1)
```

</details>

#### non-serial fd stays pending

- non-serial fd stays pending
   - Expected: req.state equals `ASYNC_PENDING`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-serial fd stays pending")
val FD_TYPE_FILE: u8 = 1
val req = simulate_serial_read_non_serial(FD_TYPE_FILE)
expect(req.state).to_equal(ASYNC_PENDING)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `58a60d680a317e2cc63fc2daab9e9b74cadf209f5a0445ad6c6c38f1c7dd43a1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58a60d680a317e2cc63fc2daab9e9b74cadf209f5a0445ad6c6c38f1c7dd43a1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58a60d680a317e2cc63fc2daab9e9b74cadf209f5a0445ad6c6c38f1c7dd43a1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/posix/async_io_serial_spec.spl
mirror: doc/06_spec/unit/os/posix/async_io_serial_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/posix/async_io_serial_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/posix/async_io_serial_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/posix/async_io_serial_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/posix/async_io_serial_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serial read request transitions ASYNC_PENDING to ASYNC_COMPLETE' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/posix/async_io_serial_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serial read result is 1 byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/posix/async_io_serial_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'non-serial fd stays pending' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
