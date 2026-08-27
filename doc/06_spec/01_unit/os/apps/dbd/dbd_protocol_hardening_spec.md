# dbd protocol + durability hardening — corrupt / hostile input (Lane HARDEN-ROBUST)

> Feeds the db-daemon protocol seam (src/os/apps/dbd/dbd_protocol.spl) and the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbd protocol + durability hardening — corrupt / hostile input (Lane HARDEN-ROBUST)

Feeds the db-daemon protocol seam (src/os/apps/dbd/dbd_protocol.spl) and the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/dbd/dbd_protocol_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Feeds the db-daemon protocol seam (src/os/apps/dbd/dbd_protocol.spl) and the
RESP wire framing it reuses (std.nogc_sync_mut.redis.server.parse_next_request)
malformed frames, and feeds the journal replay path corrupt/truncated
records. Asserts:

  * malformed RESP frames (wrong/huge length prefix, unterminated, truncated
    bulk) fail closed — parse yields nil or an empty command, never a
    fabricated partial command;
  * any corrupt or truncated journal record rejects the complete replay
    before mutation, preventing partially reconstructed durable state;
  * oversized keys/values round-trip through the real engine without
    truncation.

Complements the round-trip coverage in dbd_protocol_spec.spl.

## Scenarios

### dbd RESP framing: malformed frames fail closed

#### a truncated bulk (declared len exceeds data) parses as incomplete (nil)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- a truncated bulk (declared len exceeds data) parses as incomplete (nil)
   - Expected: _parse_argc("*1\r\n$5\r\nab\r\n") equals `-1i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a truncated bulk (declared len exceeds data) parses as incomplete (nil)")
# $5 but only 2 data bytes present -> wait for more, never fabricate
expect(_parse_argc("*1\r\n$5\r\nab\r\n")).to_equal(-1i64)
```

</details>

#### a huge array count with missing elements is incomplete (nil)

- a huge array count with missing elements is incomplete (nil)
   - Expected: _parse_argc("*999999\r\n$3\r\nfoo\r\n") equals `-1i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a huge array count with missing elements is incomplete (nil)")
expect(_parse_argc("*999999\r\n$3\r\nfoo\r\n")).to_equal(-1i64)
```

</details>

#### an unterminated array header is incomplete (nil)

- an unterminated array header is incomplete (nil)
   - Expected: _parse_argc("*3") equals `-1i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an unterminated array header is incomplete (nil)")
expect(_parse_argc("*3")).to_equal(-1i64)
```

</details>

#### a bulk header with no CRLF is incomplete (nil)

- a bulk header with no CRLF is incomplete (nil)
   - Expected: _parse_argc("*1\r\n$5") equals `-1i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a bulk header with no CRLF is incomplete (nil)")
expect(_parse_argc("*1\r\n$5")).to_equal(-1i64)
```

</details>

#### a non-numeric array count yields an empty command (dispatch -> error)

- a non-numeric array count yields an empty command (dispatch -> error)
   - Expected: _parse_argc("*abc\r\n") equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a non-numeric array count yields an empty command (dispatch -> error)")
expect(_parse_argc("*abc\r\n")).to_equal(0i64)
```

</details>

#### a negative bulk length yields a single empty arg (RESP nil bulk)

- a negative bulk length yields a single empty arg (RESP nil bulk)
   - Expected: _parse_argc("*1\r\n$-1\r\n") equals `1i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a negative bulk length yields a single empty arg (RESP nil bulk)")
expect(_parse_argc("*1\r\n$-1\r\n")).to_equal(1i64)
```

</details>

### dbd RESP framing: an empty command is rejected by the engine

#### dispatch of empty args returns a RESP error, not a crash

- dispatch of empty args returns a RESP error, not a crash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch of empty args returns a RESP error, not a crash")
var eng = DbdEngine.new()
val reply = eng.dispatch([])
assert_true(reply.starts_with("-"))
```

</details>

#### dispatch of an unknown command returns a RESP error

- dispatch of an unknown command returns a RESP error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch of an unknown command returns a RESP error")
var eng = DbdEngine.new()
val reply = eng.dispatch(["BOGUSCMD", "k"])
assert_true(reply.starts_with("-"))
```

</details>

#### a truncated SET (missing value) returns an error and does not store

- a truncated SET (missing value) returns an error and does not store
   - Expected: eng.dispatch(["GET", "k"]) equals `$-1\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a truncated SET (missing value) returns an error and does not store")
var eng = DbdEngine.new()
val reply = eng.dispatch(["SET", "k"])
assert_true(reply.starts_with("-"))
# key must NOT have been created by the rejected write
expect(eng.dispatch(["GET", "k"])).to_equal("$-1\r\n")
```

</details>

### dbd journal replay: corrupt records do not corrupt the store

#### rejects unsigned SET injection before applying preceding J1 records

- rejects unsigned SET injection before applying preceding J1 records
   - Expected: eng.dispatch(["GET", "safe"]) equals `$-1\r\n`
   - Expected: eng.dispatch(["GET", "attacker"]) equals `$-1\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unsigned SET injection before applying preceding J1 records")
val first = dbd_encode_journal_line(["SET", "safe", "yes"])
var eng = DbdEngine.new()
expect(eng.replay_journal(
    first + "\nSET attacker injected\n")).to_equal(0i64 - 1i64)
expect(eng.dispatch(["GET", "safe"])).to_equal("$-1\r\n")
expect(eng.dispatch(["GET", "attacker"])).to_equal("$-1\r\n")
```

</details>

#### rejects the complete journal before applying any partial state

- rejects the complete journal before applying any partial state
   - Expected: replayed equals `0i64 - 1i64`
   - Expected: eng.dispatch(["GET", "alpha"]) equals `$-1\r\n`
   - Expected: eng.dispatch(["GET", "beta"]) equals `$-1\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the complete journal before applying any partial state")
val journal = "SET alpha 1\nSET beta 2\nGARBAGE junk\nSET alpha 9\n"
var eng = DbdEngine.new()
val replayed = eng.replay_journal(journal)
expect(replayed).to_equal(0i64 - 1i64)
expect(eng.dispatch(["GET", "alpha"])).to_equal("$-1\r\n")
expect(eng.dispatch(["GET", "beta"])).to_equal("$-1\r\n")
```

</details>

#### a journal of only-corrupt records leaves the store empty

- a journal of only-corrupt records leaves the store empty
   - Expected: eng.replay_journal(journal) equals `0i64 - 1i64`
   - Expected: eng.dispatch(["GET", "onlykey"]) equals `$-1\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a journal of only-corrupt records leaves the store empty")
val journal = "SET\nDEL\nBOGUS x y\nSET onlykey\n"
var eng = DbdEngine.new()
expect(eng.replay_journal(journal)).to_equal(0i64 - 1i64)
expect(eng.dispatch(["GET", "onlykey"])).to_equal("$-1\r\n")
```

</details>

#### post-corruption writes still succeed (engine not wedged)

- post-corruption writes still succeed (engine not wedged)
   - Expected: eng.dispatch(["SET", "fresh", "ok"]) equals `+OK\r\n`
   - Expected: eng.dispatch(["GET", "fresh"]) equals `$2\r\nok\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("post-corruption writes still succeed (engine not wedged)")
var eng = DbdEngine.new()
eng.replay_journal("GARBAGE\nSET\n")
expect(eng.dispatch(["SET", "fresh", "ok"])).to_equal("+OK\r\n")
expect(eng.dispatch(["GET", "fresh"])).to_equal("$2\r\nok\r\n")
```

</details>

#### rejects a torn final record without a newline

- rejects a torn final record without a newline
   - Expected: eng.replay_journal("SET persisted yes") equals `0i64 - 1i64`
   - Expected: eng.dispatch(["GET", "persisted"]) equals `$-1\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a torn final record without a newline")
var eng = DbdEngine.new()
expect(eng.replay_journal("SET persisted yes")).to_equal(0i64 - 1i64)
expect(eng.dispatch(["GET", "persisted"])).to_equal("$-1\r\n")
```

</details>

### dbd journal encoding: ambiguous / oversized args

#### delimiter-bearing values are encoded without journal injection

- delimiter-bearing values are encoded without journal injection
   - Expected: dbd_decode_journal_line(spaced) equals `["SET", "k", "a b"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("delimiter-bearing values are encoded without journal injection")
val spaced = dbd_encode_journal_line(["SET", "k", "a b"])
val multiline = dbd_encode_journal_line(["SET", "k", "line1\nline2"])
expect(dbd_decode_journal_line(spaced)).to_equal(["SET", "k", "a b"])
expect(dbd_decode_journal_line(multiline)).to_equal(
    ["SET", "k", "line1\nline2"])
expect(spaced.contains("a b")).to_be(false)
expect(multiline.contains("\n")).to_be(false)
```

</details>

#### an oversized space-free value round-trips through the engine intact

- an oversized space-free value round-trips through the engine intact
   - Expected: eng.dispatch(["SET", "big", bigv]) equals `+OK\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an oversized space-free value round-trips through the engine intact")
val bigv = _big(5000)
var eng = DbdEngine.new()
expect(eng.dispatch(["SET", "big", bigv])).to_equal("+OK\r\n")
val reply = eng.dispatch(["GET", "big"])
assert_true(reply.starts_with("$5000\r\n"))
assert_true(reply.ends_with(bigv + "\r\n"))
```

</details>

#### an oversized value is rejected before journal persistence

- an oversized value is rejected before journal persistence
   - Expected: line equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an oversized value is rejected before journal persistence")
val bigv = _big(4096)
val line = dbd_encode_journal_line(["SET", "big", bigv])
expect(line).to_equal("")
```

</details>

#### invalid mutating arity is rejected before journal persistence

- invalid mutating arity is rejected before journal persistence
   - Expected: dbd_encode_journal_line(["SET", "key"]) equals ``
   - Expected: dbd_encode_journal_line(["DEL", "key", "extra"]) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalid mutating arity is rejected before journal persistence")
expect(dbd_encode_journal_line(["SET", "key"])).to_equal("")
expect(dbd_encode_journal_line(["DEL", "key", "extra"])).to_equal("")
```

</details>

#### empty keys fail closed while control-bearing values remain framed

- empty keys fail closed while control-bearing values remain framed
   - Expected: dbd_encode_journal_line(["SET", "", "value"]) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty keys fail closed while control-bearing values remain framed")
expect(dbd_encode_journal_line(["SET", "", "value"])).to_equal("")
val cr = dbd_encode_journal_line(["SET", "key", "value\rforged"])
val nul = dbd_encode_journal_line(["SET", "key", "value\0forged"])
expect(dbd_decode_journal_line(cr)).to_equal(
    ["SET", "key", "value\rforged"])
expect(dbd_decode_journal_line(nul)).to_equal(
    ["SET", "key", "value\0forged"])
```

</details>

### dbd production startup admission

#### advertises implemented auth mechanics without hiding boot blockers

- advertises implemented auth mechanics without hiding boot blockers
   - Expected: dbd_dbfs_persistence_blocker() equals `dbfs-engine-owner-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("advertises implemented auth mechanics without hiding boot blockers")
expect(dbd_production_startup_ready()).to_be(false)
expect(dbd_production_startup_blocker()).to_equal(
    "boot-mutable-credential-owner-unavailable")
assert_true(DBD_CAPABILITY_STATE.contains(
    "auth=DigestVerifierImplementedUnprovisionedV1"))
assert_true(not DBD_CAPABILITY_STATE.contains(
    "auth=ProvisionedDigestV1"))
assert_true(DBD_CAPABILITY_STATE.contains(
    "filesystem_launch=VerifiedArtifactSecurityGatedV1"))
assert_true(DBD_CAPABILITY_STATE.contains(
    "journal=ChecksummedBase64V1"))
assert_true(DBD_CAPABILITY_STATE.contains(
    "auth_framing=DbdMutableAuthRequestOwnerV1"))
assert_true(DBD_CAPABILITY_STATE.contains("tls=Blocked"))
assert_true(DBD_CAPABILITY_STATE.contains(
    "tls_handshake_authority=BlockedCertificatePrivateKeyEntropyOwner"))
assert_true(DBD_CAPABILITY_STATE.contains("live_dbfs_durability=Blocked"))
expect(dbd_dbfs_persistence_ready()).to_be(false)
expect(dbd_dbfs_persistence_blocker()).to_equal("dbfs-engine-owner-unavailable")
```

</details>

#### redacts a whole credential-bearing diagnostic

- redacts a whole credential-bearing diagnostic


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("redacts a whole credential-bearing diagnostic")
expect(dbd_redact_diagnostic("AUTH operator super-secret")).to_equal(
    "[dbd] sensitive diagnostic redacted"
)
expect(dbd_redact_diagnostic("[dbd] backend=vfs-log")).to_equal(
    "[dbd] backend=vfs-log"
)
expect(dbd_redact_diagnostic("authentication-owner-unavailable")).to_equal(
    "authentication-owner-unavailable"
)
```

</details>

### dbd session budget: cumulative backpressure

#### admits exactly the byte quota and rejects overflow without wraparound

- admits exactly the byte quota and rejects overflow without wraparound


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits exactly the byte quota and rejects overflow without wraparound")
var budget = DbdSessionBudget.new()
expect(budget.admit_receive(DBD_MAX_SESSION_BYTES)).to_be(true)
expect(budget.admit_receive(1)).to_be(false)
var oversized = DbdSessionBudget.new()
expect(oversized.admit_receive(DBD_MAX_SESSION_BYTES + 1)).to_be(false)
```

</details>

#### admits exactly the request quota

- admits exactly the request quota


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits exactly the request quota")
var budget = DbdSessionBudget.new()
var admitted: i64 = 0
while admitted < DBD_MAX_REQUESTS_PER_SESSION:
    expect(budget.admit_request()).to_be(true)
    admitted = admitted + 1
expect(budget.admit_request()).to_be(false)
```

</details>

#### bounds cumulative response bytes and rejects negative sizes

- bounds cumulative response bytes and rejects negative sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bounds cumulative response bytes and rejects negative sizes")
var budget = DbdSessionBudget.new()
expect(budget.admit_response(DBD_MAX_RESPONSE_BYTES_PER_SESSION)).to_be(true)
expect(budget.admit_response(1)).to_be(false)
var negative = DbdSessionBudget.new()
expect(negative.admit_response(0i64 - 1i64)).to_be(false)
expect(negative.admit_response(DBD_MAX_RESPONSE_BYTES_PER_SESSION + 1)).to_be(false)
```

</details>

#### a closed session rejects every subsequent admission

- a closed session rejects every subsequent admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a closed session rejects every subsequent admission")
var budget = DbdSessionBudget.new()
budget.close()
expect(budget.admit_receive(1)).to_be(false)
expect(budget.admit_request()).to_be(false)
expect(budget.admit_response(1)).to_be(false)
```

</details>

### dbd persistence owner state: successive verified mutations

#### retains byte and record accounting across successive commits

- retains byte and record accounting across successive commits
   - Expected: state.record_count equals `2i64`
   - Expected: state.journal_bytes equals `20i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retains byte and record accounting across successive commits")
var state = DbdPersistenceBudget.new()
expect(state.commit_verified(8)).to_be(true)
expect(state.commit_verified(12)).to_be(true)
expect(state.record_count).to_equal(2i64)
expect(state.journal_bytes).to_equal(20i64)
```

</details>

#### rejects both record-cap and byte-cap exhaustion

- rejects both record-cap and byte-cap exhaustion


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects both record-cap and byte-cap exhaustion")
var record_full = DbdPersistenceBudget.restored(
    DBD_MAX_JOURNAL_RECORDS, 0)
expect(record_full.commit_verified(1)).to_be(false)
var byte_full = DbdPersistenceBudget.restored(0, DBD_MAX_JOURNAL_BYTES)
expect(byte_full.commit_verified(1)).to_be(false)
```

</details>

#### an unhealthy owner cannot resume mutation admission

- an unhealthy owner cannot resume mutation admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an unhealthy owner cannot resume mutation admission")
var state = DbdPersistenceBudget.new()
state.mark_unhealthy()
expect(state.commit_verified(1)).to_be(false)
```

</details>

### dbd configured credential provider and per-session identity

#### admits the configured principal and credential without retaining raw bytes

- admits the configured principal and credential without retaining raw bytes
   - Expected: provider.principal equals `operator`
   - Expected: session.identity equals `operator`
   - Expected: session.identity_generation equals `1i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits the configured principal and credential without retaining raw bytes")
var provider = DbdCredentialProvider.new()
val configured = provider.configure_bytes("operator", _credential(17u8))
expect(configured).to_be(true)
expect(provider.configured).to_be(true)
expect(provider.principal).to_equal("operator")
var session = DbdAuthSession.new(1)
val accepted = session.authenticate(provider, "operator", _credential(17u8))
expect(accepted).to_be(true)
expect(session.can_dispatch()).to_be(true)
expect(session.identity).to_equal("operator")
expect(session.identity_generation).to_equal(1i64)
```

</details>

#### rejects wrong principal, wrong credential, and unconfigured providers

- rejects wrong principal, wrong credential, and unconfigured providers


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects wrong principal, wrong credential, and unconfigured providers")
var provider = DbdCredentialProvider.new()
provider.configure_bytes("operator", _credential(23u8))
var wrong_principal = DbdAuthSession.new(2)
expect(wrong_principal.authenticate(
    provider, "other", _credential(23u8))).to_be(false)
var wrong_credential = DbdAuthSession.new(3)
expect(wrong_credential.authenticate(
    provider, "operator", _credential(24u8))).to_be(false)
var unconfigured = DbdAuthSession.new(4)
expect(unconfigured.authenticate(
    DbdCredentialProvider.new(), "operator", _credential(23u8)
)).to_be(false)
```

</details>

#### closes a session after the bounded failed-attempt budget

- closes a session after the bounded failed-attempt budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closes a session after the bounded failed-attempt budget")
var provider = DbdCredentialProvider.new()
provider.configure_bytes("operator", _credential(29u8))
var session = DbdAuthSession.new(5)
var attempt: i64 = 0
while attempt < DBD_MAX_AUTH_ATTEMPTS_PER_SESSION:
    expect(session.authenticate(
        provider, "operator", _credential(30u8))).to_be(false)
    attempt = attempt + 1
expect(session.closed).to_be(true)
expect(session.authenticate(
    provider, "operator", _credential(29u8))).to_be(false)
```

</details>

#### rejects oversized credentials before hashing unbounded input

- rejects oversized credentials before hashing unbounded input


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects oversized credentials before hashing unbounded input")
var provider = DbdCredentialProvider.new()
expect(provider.configure_bytes("operator", [1u8])).to_be(false)
expect(provider.configure_bytes(
    "operator", _big_bytes(DBD_MAX_CREDENTIAL_BYTES + 1))).to_be(false)
expect(provider.configured).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
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

- Canonical SPipe generation for source `dda23152dc776ad784859496d41fcb7ab0fddb7a92fe2e124b40b239661e4da8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dda23152dc776ad784859496d41fcb7ab0fddb7a92fe2e124b40b239661e4da8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dda23152dc776ad784859496d41fcb7ab0fddb7a92fe2e124b40b239661e4da8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/apps/dbd/dbd_protocol_hardening_spec.spl
mirror: doc/06_spec/01_unit/os/apps/dbd/dbd_protocol_hardening_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/dbd/dbd_protocol_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/dbd/dbd_protocol_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/dbd/dbd_protocol_hardening_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a truncated bulk (declared len exceeds data) parses as incomplete (nil)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/dbd/dbd_protocol_hardening_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a huge array count with missing elements is incomplete (nil)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/dbd/dbd_protocol_hardening_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an unterminated array header is incomplete (nil)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
