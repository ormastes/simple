# DBD authenticated command byte ingress

> Exercises the fixed-capacity post-authentication RESP owner without inspecting

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DBD authenticated command byte ingress

Exercises the fixed-capacity post-authentication RESP owner without inspecting

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/dbd/dbd_command_ingress_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises the fixed-capacity post-authentication RESP owner without inspecting
its source.  Complete frames are returned in order, incomplete bytes remain
mutable, repeated AUTH is classified before text conversion, and one-byte
fragmentation has bounded byte work.

## Scenarios

### DBD authenticated command byte framing

#### frames a command fragmented one byte at a time with linear work

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- frames a command fragmented one byte at a time with linear work
   - Expected: frame.bytes equals `command`
   - Expected: frame.retained_nonzero_byte_count() equals `0i64`
   - Expected: owner.remaining_byte_count() equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frames a command fragmented one byte at a time with linear work")
val command = _large_set()
val owner = DbdAuthenticatedRespIngressV1.new()
var index: i64 = 0
while index < command.len().to_i64():
    expect(owner.ingest(command.slice(
        index.to_u64(), (index + 1).to_u64()
    ))).to_equal(DbdCommandIngressStatusV1.Accepted)
    index = index + 1
match owner.take_next():
    case nil:
        fail("complete one-byte-fragmented command was not published")
    case Some(frame):
        expect(frame.bytes).to_equal(command)
        expect(frame.auth_command).to_be(false)
        expect(frame.zeroize_owned_bytes()).to_equal(
            command.len().to_i64())
        expect(frame.retained_nonzero_byte_count()).to_equal(0i64)
expect(owner.byte_work()).to_be_less_than(
    command.len().to_i64() * 3 + 1)
expect(owner.remaining_byte_count()).to_equal(0i64)
expect(owner.last_take_zeroized_owned_bytes()).to_be(true)
```

</details>

#### publishes coalesced commands in wire order

- publishes coalesced commands in wire order


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("publishes coalesced commands in wire order")
val ping = "*1\r\n$4\r\nPING\r\n".bytes()
val get = "*2\r\n$3\r\nGET\r\n$3\r\nkey\r\n".bytes()
val owner = DbdAuthenticatedRespIngressV1.new()
expect(owner.ingest(_append(ping, get))).to_equal(
    DbdCommandIngressStatusV1.Accepted)
match owner.take_next():
    case nil: fail("first coalesced command missing")
    case Some(frame): expect(frame.bytes).to_equal(ping)
match owner.take_next():
    case nil: fail("second coalesced command missing")
    case Some(frame): expect(frame.bytes).to_equal(get)
expect(owner.take_next()).to_be_nil()
```

</details>

#### retains an incomplete frame without publishing it

- retains an incomplete frame without publishing it
   - Expected: owner.remaining_byte_count() equals `partial.len().to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retains an incomplete frame without publishing it")
val owner = DbdAuthenticatedRespIngressV1.new()
val partial = "*2\r\n$3\r\nGET\r\n$5\r\npar".bytes()
expect(owner.ingest(partial)).to_equal(
    DbdCommandIngressStatusV1.Accepted)
expect(owner.take_next()).to_be_nil()
expect(owner.remaining_byte_count()).to_equal(partial.len().to_i64())
```

</details>

#### rejects malformed framing and a buffer larger than its fixed bound

- rejects malformed framing and a buffer larger than its fixed bound
   - Expected: malformed_owner.remaining_byte_count() equals `0i64`
   - Expected: bounded_owner.remaining_byte_count() equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed framing and a buffer larger than its fixed bound")
val malformed_owner = DbdAuthenticatedRespIngressV1.new()
expect(malformed_owner.ingest("*1\rX".bytes())).to_equal(
    DbdCommandIngressStatusV1.Malformed)
expect(malformed_owner.take_next()).to_be_nil()
expect(malformed_owner.last_failure_zeroized_owned_bytes()).to_be(true)
expect(malformed_owner.remaining_byte_count()).to_equal(0i64)

var oversized: [u8] = []
var index: i64 = 0
while index <= DBD_MAX_SESSION_BYTES:
    oversized.push(65u8)
    index = index + 1
val bounded_owner = DbdAuthenticatedRespIngressV1.new()
expect(bounded_owner.ingest(oversized)).to_equal(
    DbdCommandIngressStatusV1.Overflow)
expect(bounded_owner.last_failure_zeroized_owned_bytes()).to_be(true)
expect(bounded_owner.remaining_byte_count()).to_equal(0i64)
```

</details>

#### classifies RESP and inline AUTH before immutable parsing

- classifies RESP and inline AUTH before immutable parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies RESP and inline AUTH before immutable parsing")
val resp_auth = "*2\r\n$4\r\nAUTH\r\n$1\r\nx\r\n".bytes()
val inline_auth = "auth x\r\n".bytes()
val owner = DbdAuthenticatedRespIngressV1.new()
expect(owner.ingest(_append(resp_auth, inline_auth))).to_equal(
    DbdCommandIngressStatusV1.Accepted)
match owner.take_next():
    case nil: fail("RESP AUTH frame missing")
    case Some(frame): expect(frame.auth_command).to_be(true)
match owner.take_next():
    case nil: fail("inline AUTH frame missing")
    case Some(frame): expect(frame.auth_command).to_be(true)
```

</details>

#### wipes incomplete owned bytes when the session closes

- wipes incomplete owned bytes when the session closes
   - Expected: owner.remaining_byte_count() equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wipes incomplete owned bytes when the session closes")
val owner = DbdAuthenticatedRespIngressV1.new()
val partial = "*2\r\n$3\r\nGET\r\n$8\r\nsecret".bytes()
expect(owner.ingest(partial)).to_equal(
    DbdCommandIngressStatusV1.Accepted)
owner.close()
expect(owner.last_close_wiped_byte_count()).to_equal(
    partial.len().to_i64())
expect(owner.last_close_zeroized_owned_bytes()).to_be(true)
expect(owner.remaining_byte_count()).to_equal(0i64)
expect(owner.ingest([1u8])).to_equal(
    DbdCommandIngressStatusV1.Closed)
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `37bca8f37d46d03d7664693bf33b9ffcbca9827ed3179bada56735a4e7244d2f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `37bca8f37d46d03d7664693bf33b9ffcbca9827ed3179bada56735a4e7244d2f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `37bca8f37d46d03d7664693bf33b9ffcbca9827ed3179bada56735a4e7244d2f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/apps/dbd/dbd_command_ingress_spec.spl
mirror: doc/06_spec/01_unit/os/apps/dbd/dbd_command_ingress_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/dbd/dbd_command_ingress_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/dbd/dbd_command_ingress_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/dbd/dbd_command_ingress_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'frames a command fragmented one byte at a time with linear work' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/dbd/dbd_command_ingress_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes coalesced commands in wire order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/dbd/dbd_command_ingress_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains an incomplete frame without publishing it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
