# dbd protocol + durability (Lane C2)

> Proves the in-guest db daemon's protocol/journal/replay logic in-process,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbd protocol + durability (Lane C2)

Proves the in-guest db daemon's protocol/journal/replay logic in-process,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/dbd/dbd_protocol_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the in-guest db daemon's protocol/journal/replay logic in-process,
without a socket or a mounted disk, by driving the pure seam
(src/os/apps/dbd/dbd_protocol.spl) that the freestanding transport
(src/os/apps/dbd/dbd.spl) sits on top of.

The db engine itself is the REAL Simple RESP server
(std.nogc_sync_mut.redis.server.RedisServer) — the same engine
src/app/redis_server/main.spl runs hosted. These specs assert the durability
seam this lane adds: a write-ahead journal of mutating commands that,
replayed through that same RedisServer.dispatch(), reconstructs the store —
which is exactly the reboot-persistence guarantee (write journal, read it
back after reboot, replay).

## Scenarios

### dbd protocol: mutation classification

#### SET and DEL are mutating (case-insensitive)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- SET and DEL are mutating (case-insensitive)
   - Expected: dbd_command_is_mutating("SET") is true
   - Expected: dbd_command_is_mutating("DEL") is true
   - Expected: dbd_command_is_mutating("set") is true
   - Expected: dbd_command_is_mutating("del") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SET and DEL are mutating (case-insensitive)")
expect(dbd_command_is_mutating("SET")).to_equal(true)
expect(dbd_command_is_mutating("DEL")).to_equal(true)
expect(dbd_command_is_mutating("set")).to_equal(true)
expect(dbd_command_is_mutating("del")).to_equal(true)
```

</details>

#### reads are not mutating

- reads are not mutating
   - Expected: dbd_command_is_mutating("GET") is false
   - Expected: dbd_command_is_mutating("PING") is false
   - Expected: dbd_command_is_mutating("EXISTS") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads are not mutating")
expect(dbd_command_is_mutating("GET")).to_equal(false)
expect(dbd_command_is_mutating("PING")).to_equal(false)
expect(dbd_command_is_mutating("EXISTS")).to_equal(false)
```

</details>

### dbd protocol: journal encode/decode round-trip

#### encodes args as an integrity-bound J1 line

- encodes args as an integrity-bound J1 line
   - Expected: encoded.starts_with("J1 ") is true
   - Expected: dbd_decode_journal_line(encoded) equals `["SET", "k", "v"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes args as an integrity-bound J1 line")
val encoded = dbd_encode_journal_line(["SET", "k", "v"])
expect(encoded.starts_with("J1 ")).to_equal(true)
expect(dbd_decode_journal_line(encoded)).to_equal(["SET", "k", "v"])
```

</details>

#### round-trips spaces, newlines, empty values, and Unicode

- round-trips spaces, newlines, empty values, and Unicode
   - Expected: encoded.starts_with("J1 ") is true
   - Expected: dbd_decode_journal_line(encoded) equals `["SET", "k", value]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips spaces, newlines, empty values, and Unicode")
val values = ["a b", "line1\nline2", "", "雪"]
for value in values:
    val encoded = dbd_encode_journal_line(["SET", "k", value])
    expect(encoded.starts_with("J1 ")).to_equal(true)
    expect(dbd_decode_journal_line(encoded)).to_equal(["SET", "k", value])
```

</details>

#### rejects an unsigned legacy line instead of bypassing J1 integrity

- rejects an unsigned legacy line instead of bypassing J1 integrity
   - Expected: args.len() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unsigned legacy line instead of bypassing J1 integrity")
val args = dbd_decode_journal_line("SET k v")
expect(args.len()).to_equal(0u64)
```

</details>

#### encode then decode is an identity for well-formed args

- encode then decode is an identity for well-formed args
   - Expected: decoded.len() equals `2u64`
   - Expected: decoded[0] equals `DEL`
   - Expected: decoded[1] equals `mykey`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encode then decode is an identity for well-formed args")
val encoded = dbd_encode_journal_line(["DEL", "mykey"])
val decoded = dbd_decode_journal_line(encoded)
expect(decoded.len()).to_equal(2u64)
expect(decoded[0]).to_equal("DEL")
expect(decoded[1]).to_equal("mykey")
```

</details>

#### rejects a modified integrity-bound record

- rejects a modified integrity-bound record
   - Expected: dbd_decode_journal_line(tampered).len() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a modified integrity-bound record")
val encoded = dbd_encode_journal_line(["SET", "key", "value"])
val tampered = encoded.substring(0, encoded.len() - 1) + "A"
expect(dbd_decode_journal_line(tampered).len()).to_equal(0u64)
```

</details>

### dbd engine: real RESP dispatch

#### SET then GET returns the value via the real engine

- SET then GET returns the value via the real engine
   - Expected: eng.dispatch(["SET", "k", "v"]) equals `+OK\r\n`
   - Expected: eng.dispatch(["GET", "k"]) equals `$1\r\nv\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SET then GET returns the value via the real engine")
var eng = DbdEngine.new()
expect(eng.dispatch(["SET", "k", "v"])).to_equal("+OK\r\n")
expect(eng.dispatch(["GET", "k"])).to_equal("$1\r\nv\r\n")
```

</details>

#### GET on an unknown key returns RESP nil

- GET on an unknown key returns RESP nil
   - Expected: eng.dispatch(["GET", "missing"]) equals `$-1\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GET on an unknown key returns RESP nil")
var eng = DbdEngine.new()
expect(eng.dispatch(["GET", "missing"])).to_equal("$-1\r\n")
```

</details>

### dbd engine: journal replay = reboot persistence

#### replaying a journal reconstructs the store through the real engine

- replaying a journal reconstructs the store through the real engine
   - Expected: replayed equals `4i64`
   - Expected: eng.dispatch(["GET", "alpha"]) equals `$1\r\n9\r\n`
   - Expected: eng.dispatch(["GET", "beta"]) equals `$-1\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaying a journal reconstructs the store through the real engine")
# Simulate integrity-bound durable records written on a previous boot.
val journal =
    dbd_encode_journal_line(["SET", "alpha", "1"]) + "\n" +
    dbd_encode_journal_line(["SET", "beta", "2"]) + "\n" +
    dbd_encode_journal_line(["SET", "alpha", "9"]) + "\n" +
    dbd_encode_journal_line(["DEL", "beta"]) + "\n"
var eng = DbdEngine.new()
val replayed = eng.replay_journal(journal)
expect(replayed).to_equal(4i64)
# alpha was overwritten to 9, beta was deleted.
expect(eng.dispatch(["GET", "alpha"])).to_equal("$1\r\n9\r\n")
expect(eng.dispatch(["GET", "beta"])).to_equal("$-1\r\n")
```

</details>

#### empty journal replays nothing

- empty journal replays nothing
   - Expected: eng.replay_journal("") equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty journal replays nothing")
var eng = DbdEngine.new()
expect(eng.replay_journal("")).to_equal(0i64)
```

</details>

#### post-replay writes coexist with replayed state (durability continuity)

- post-replay writes coexist with replayed state (durability continuity)
   - Expected: replayed equals `1i64`
   - Expected: eng.dispatch(["SET", "fresh", "no"]) equals `+OK\r\n`
   - Expected: eng.dispatch(["GET", "persisted"]) equals `$3\r\nyes\r\n`
   - Expected: eng.dispatch(["GET", "fresh"]) equals `$2\r\nno\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("post-replay writes coexist with replayed state (durability continuity)")
var eng = DbdEngine.new()
val replayed = eng.replay_journal(
    dbd_encode_journal_line(["SET", "persisted", "yes"]) + "\n")
expect(replayed).to_equal(1i64)
expect(eng.dispatch(["SET", "fresh", "no"])).to_equal("+OK\r\n")
expect(eng.dispatch(["GET", "persisted"])).to_equal("$3\r\nyes\r\n")
expect(eng.dispatch(["GET", "fresh"])).to_equal("$2\r\nno\r\n")
```

</details>

#### reboots a delimiter-bearing value from its canonical durable record

- reboots a delimiter-bearing value from its canonical durable record
   - Expected: eng.replay_journal(line + "\n") equals `1i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reboots a delimiter-bearing value from its canonical durable record")
val line = dbd_encode_journal_line(
    ["SET", "message", "hello from SimpleOS\nfilesystem"])
var eng = DbdEngine.new()
expect(eng.replay_journal(line + "\n")).to_equal(1i64)
expect(eng.dispatch(["GET", "message"])).to_equal(
    "$30\r\nhello from SimpleOS\nfilesystem\r\n")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `f8d70f09129b84521593f86d4af00219624e417594e8d388d97cfa974d029066`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f8d70f09129b84521593f86d4af00219624e417594e8d388d97cfa974d029066`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f8d70f09129b84521593f86d4af00219624e417594e8d388d97cfa974d029066`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/apps/dbd/dbd_protocol_spec.spl
mirror: doc/06_spec/01_unit/os/apps/dbd/dbd_protocol_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/dbd/dbd_protocol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/dbd/dbd_protocol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/dbd/dbd_protocol_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SET and DEL are mutating (case-insensitive)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/dbd/dbd_protocol_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads are not mutating' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/dbd/dbd_protocol_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes args as an integrity-bound J1 line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
