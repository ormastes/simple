# DBD TLS record ownership

> Exercises the shared bounded TLS record framing through DBD's real AEAD owner.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DBD TLS record ownership

Exercises the shared bounded TLS record framing through DBD's real AEAD owner.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/dbd/dbd_tls_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises the shared bounded TLS record framing through DBD's real AEAD owner.
It proves that split/coalesced ciphertext is authenticated before plaintext is
released and that failed authentication never advances the receive sequence.

## Scenarios

### DBD TLS authenticated record framing

#### mutates one session owner across one-byte ingress with bounded work

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- mutates one session owner across one-byte ingress with bounded work
   - Expected: ingress.status equals `DbdTlsIngressStatusV1.NeedMore`
   - Expected: session.stream.sequence() equals `0i64`
   - Expected: final_ingress.plaintext_frames equals `[[77u8, 78u8]]`
   - Expected: session.stream.sequence() equals `1i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mutates one session owner across one-byte ingress with bounded work")
var session = DbdTlsSessionV1.from_context(_context()).unwrap()
val record = _client_record(0u64, [77u8, 78u8])
var index: i64 = 0
var prior_work: i64 = 0
while index < record.len().to_i64() - 1:
    val ingress = session.ingest(
        record.slice(index.to_u64(), (index + 1).to_u64()))
    expect(ingress.status).to_equal(DbdTlsIngressStatusV1.NeedMore)
    expect(session.stream.sequence()).to_equal(0i64)
    expect(session.stream.byte_work()).to_be_greater_than(prior_work)
    prior_work = session.stream.byte_work()
    index = index + 1
val final_ingress = session.ingest(
    record.slice(index.to_u64(), record.len()))
expect(final_ingress.status).to_equal(
    DbdTlsIngressStatusV1.Authenticated)
expect(final_ingress.plaintext_frames).to_equal([[77u8, 78u8]])
expect(session.stream.sequence()).to_equal(1i64)
expect(session.stream.has_pending_proposal()).to_be(false)
expect(session.stream.byte_work()).to_be_greater_than(prior_work)
```

</details>

#### retains split ciphertext and releases plaintext only after authentication

- retains split ciphertext and releases plaintext only after authentication
   - Expected: first.status equals `DbdTlsIngressStatusV1.NeedMore`
   - Expected: first.plaintext_frames.len() equals `0u64`
   - Expected: session.stream.sequence() equals `0i64`
   - Expected: first.remainder_length equals `split_at`
   - Expected: second.status equals `DbdTlsIngressStatusV1.Authenticated`
   - Expected: second.plaintext_frames equals `[[65u8, 66u8, 67u8]]`
   - Expected: second.remainder_length equals `0i64`
   - Expected: session.stream.sequence() equals `1i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retains split ciphertext and releases plaintext only after authentication")
var session = DbdTlsSessionV1.from_context(_context()).unwrap()
val record = _client_record(0u64, [65u8, 66u8, 67u8])
val split_at = 7
val first = session.ingest(record.slice(0, split_at))
expect(first.status).to_equal(DbdTlsIngressStatusV1.NeedMore)
expect(first.plaintext_frames.len()).to_equal(0u64)
expect(session.stream.sequence()).to_equal(0i64)
expect(first.remainder_length).to_equal(split_at)

val second = session.ingest(record.slice(split_at, record.len()))
expect(second.status).to_equal(DbdTlsIngressStatusV1.Authenticated)
expect(second.plaintext_frames).to_equal([[65u8, 66u8, 67u8]])
expect(second.remainder_length).to_equal(0i64)
expect(session.stream.sequence()).to_equal(1i64)
```

</details>

#### authenticates coalesced records and commits each sequence in order

- authenticates coalesced records and commits each sequence in order
   - Expected: ingested.status equals `DbdTlsIngressStatusV1.Authenticated`
   - Expected: ingested.authenticated_record_count equals `2i64`
   - Expected: ingested.plaintext_frames equals `[[1u8], [2u8, 3u8]]`
   - Expected: session.stream.sequence() equals `2i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("authenticates coalesced records and commits each sequence in order")
var session = DbdTlsSessionV1.from_context(_context()).unwrap()
val records = _client_record(0u64, [1u8]) +
    _client_record(1u64, [2u8, 3u8])
val ingested = session.ingest(records)
expect(ingested.status).to_equal(DbdTlsIngressStatusV1.Authenticated)
expect(ingested.authenticated_record_count).to_equal(2i64)
expect(ingested.plaintext_frames).to_equal([[1u8], [2u8, 3u8]])
expect(session.stream.sequence()).to_equal(2i64)
```

</details>

### DBD TLS fail-closed record admission

#### rejects a forged tag without advancing the receive sequence

- rejects a forged tag without advancing the receive sequence
   - Expected: ingested.plaintext_frames.len() equals `0u64`
   - Expected: session.stream.sequence() equals `0i64`
   - Expected: session.status equals `DbdTlsSessionStatusV1.Failed`
   - Expected: session.client_key.key.len() equals `0u64`
   - Expected: session.server_key.key.len() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a forged tag without advancing the receive sequence")
var session = DbdTlsSessionV1.from_context(_context()).unwrap()
var forged = _client_record(0u64, [9u8, 8u8, 7u8])
val last = forged.len() - 1u64
forged[last] = forged[last] ^ 1u8
val ingested = session.ingest(forged)
expect(ingested.status).to_equal(
    DbdTlsIngressStatusV1.AuthenticationFailed)
expect(ingested.plaintext_frames.len()).to_equal(0u64)
expect(session.stream.sequence()).to_equal(0i64)
expect(session.status).to_equal(DbdTlsSessionStatusV1.Failed)
expect(session.client_key.key.len()).to_equal(0u64)
expect(session.server_key.key.len()).to_equal(0u64)
```

</details>

#### maps malformed framing, byte-capacity overflow, and sequence exhaustion

- maps malformed framing, byte-capacity overflow, and sequence exhaustion
   - Expected: malformed.status equals `DbdTlsIngressStatusV1.Malformed`
   - Expected: overflow.status equals `DbdTlsIngressStatusV1.Overflow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps malformed framing, byte-capacity overflow, and sequence exhaustion")
var malformed_session = DbdTlsSessionV1.from_context(_context()).unwrap()
val malformed = malformed_session.ingest(
    [22u8, TLS_VERSION_MAJOR_V1.to_u8(),
        TLS_VERSION_MINOR_V1.to_u8(), 0u8,
        TLS_AEAD_TAG_LENGTH_V1.to_u8()])
expect(malformed.status).to_equal(DbdTlsIngressStatusV1.Malformed)

var fragment_session = DbdTlsSessionV1.from_context(_context()).unwrap()
val overflow = fragment_session.ingest(
    _bytes(0u8, TLS_MAX_RX_BUFFER_LENGTH_V1 + 1))
expect(overflow.status).to_equal(DbdTlsIngressStatusV1.Overflow)

var sequence_session = DbdTlsSessionV1.from_context(
    _context(TLS_MAX_SEQUENCE_V1.to_u64())).unwrap()
val record_at_limit = _bytes(0u8, TLS_AEAD_TAG_LENGTH_V1)
val exhausted = sequence_session.ingest(
    [TLS_APPLICATION_DATA_TYPE_V1.to_u8(),
        TLS_VERSION_MAJOR_V1.to_u8(), TLS_VERSION_MINOR_V1.to_u8(),
        0u8, TLS_AEAD_TAG_LENGTH_V1.to_u8()] + record_at_limit
)
expect(exhausted.status).to_equal(
    DbdTlsIngressStatusV1.SequenceExhausted)
```

</details>

#### rejects unsupported cipher and malformed traffic-key shapes

- rejects unsupported cipher and malformed traffic-key shapes


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unsupported cipher and malformed traffic-key shapes")
var unsupported = _context()
unsupported.cipher_suite = 0x1302u16
expect(DbdTlsSessionV1.from_context(unsupported).is_err()).to_be(true)
var malformed_keys = _context()
malformed_keys.client_app_key = [1u8]
expect(DbdTlsSessionV1.from_context(malformed_keys).is_err()).to_be(true)
val invalid_sequence = _context(
    TLS_MAX_SEQUENCE_V1.to_u64() + 1u64)
expect(DbdTlsSessionV1.from_context(
    invalid_sequence).is_err()).to_be(true)
```

</details>

#### rejects authenticated records carrying a non-application inner type

- rejects authenticated records carrying a non-application inner type
   - Expected: ingested.plaintext_frames.len() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects authenticated records carrying a non-application inner type")
var session = DbdTlsSessionV1.from_context(_context()).unwrap()
val handshake_inner = _client_record_with_type(
    0u64, 22u8, [1u8, 2u8])
val ingested = session.ingest(handshake_inner)
expect(ingested.status).to_equal(
    DbdTlsIngressStatusV1.UnexpectedContentType)
expect(ingested.plaintext_frames.len()).to_equal(0u64)
```

</details>

#### does not reopen an explicitly closed session

- does not reopen an explicitly closed session
   - Expected: ingested.plaintext_frames.len() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not reopen an explicitly closed session")
var session = DbdTlsSessionV1.from_context(_context()).unwrap()
session.close()
val ingested = session.ingest(_client_record(0u64, [1u8]))
expect(ingested.status).to_equal(
    DbdTlsIngressStatusV1.SessionClosed)
expect(ingested.plaintext_frames.len()).to_equal(0u64)
```

</details>

### DBD TLS encrypted response ownership

#### delivers authenticated TLS plaintext to the mutable AUTH owner

- delivers authenticated TLS plaintext to the mutable AUTH owner
   - Expected: ingress.plaintext_frames.len() equals `1u64`
   - Expected: ingress.retained_plaintext_nonzero_byte_count() equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("delivers authenticated TLS plaintext to the mutable AUTH owner")
var provider = DbdCredentialProvider.new()
expect(provider.configure_bytes(
    "operator", _bytes(41u8, 32))).to_be(true)
var tls = DbdTlsSessionV1.from_context(_context()).unwrap()
val request = _auth_request(_bytes(41u8, 32))
var ingress = tls.ingest(_client_record(0u64, request))
expect(ingress.status).to_equal(
    DbdTlsIngressStatusV1.Authenticated)
expect(ingress.plaintext_frames.len()).to_equal(1u64)
val auth_owner = DbdMutableAuthRequestOwnerV1.new(71)
expect(auth_owner.ingest(
    provider, ingress.plaintext_frames[0]
)).to_equal(DbdAuthIngressStatusV1.Authenticated)
expect(auth_owner.can_dispatch()).to_be(true)
expect(auth_owner.last_credential_was_zeroized()).to_be(true)
expect(ingress.zeroize_plaintext_frame(0u64)).to_equal(
    request.len().to_i64())
expect(ingress.retained_plaintext_nonzero_byte_count()).to_equal(0i64)
```

</details>

#### seals a fixed authentication reply as decryptable application data

- seals a fixed authentication reply as decryptable application data
   - Expected: plaintext equals `"+OK\r\n".bytes()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("seals a fixed authentication reply as decryptable application data")
var session = DbdTlsSessionV1.from_context(_context()).unwrap()
val record = session.seal_application("+OK\r\n".bytes())
val opened = record13_decrypt_for_suite(
    CIPHER_AES_128_GCM_SHA256,
    RecordKey(key: _bytes(5u8, 16), iv: _bytes(6u8, 12)),
    0u64,
    record
)
match opened:
    case RecordResult.Err(_):
        fail("sealed authentication reply did not authenticate")
    case RecordResult.Ok(content_type, plaintext):
        expect(content_type).to_equal(
            TLS_APPLICATION_DATA_TYPE_V1.to_u8())
        expect(plaintext).to_equal("+OK\r\n".bytes())
```

</details>

#### commits the send sequence only when a record is emitted

- commits the send sequence only when a record is emitted
   - Expected: session.server_sequence equals `1i64`
   - Expected: rejected.len() equals `0u64`
   - Expected: session.server_sequence equals `1i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("commits the send sequence only when a record is emitted")
var session = DbdTlsSessionV1.from_context(_context()).unwrap()
val record = session.seal_application([43u8, 79u8, 75u8])
expect(record.len() > 0).to_be(true)
expect(session.server_sequence).to_equal(1i64)
val rejected = session.seal_application([])
expect(rejected.len()).to_equal(0u64)
expect(session.server_sequence).to_equal(1i64)
```

</details>

#### releases traffic-key references when the session closes

- releases traffic-key references when the session closes
   - Expected: session.status equals `DbdTlsSessionStatusV1.Closed`
   - Expected: session.client_key.key.len() equals `0u64`
   - Expected: session.server_key.key.len() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("releases traffic-key references when the session closes")
var session = DbdTlsSessionV1.from_context(_context()).unwrap()
session.close()
expect(session.status).to_equal(DbdTlsSessionStatusV1.Closed)
expect(session.client_key.key.len()).to_equal(0u64)
expect(session.server_key.key.len()).to_equal(0u64)
```

</details>

#### fails closed instead of wrapping an exhausted send sequence

- fails closed instead of wrapping an exhausted send sequence
   - Expected: session.seal_application([1u8]).len() equals `0u64`
   - Expected: session.server_sequence equals `TLS_MAX_SEQUENCE_V1`
   - Expected: session.status equals `DbdTlsSessionStatusV1.Failed`
   - Expected: session.server_key.key.len() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed instead of wrapping an exhausted send sequence")
var context = _context()
context.server_seq = TLS_MAX_SEQUENCE_V1.to_u64()
var session = DbdTlsSessionV1.from_context(context).unwrap()
expect(session.seal_application([1u8]).len()).to_equal(0u64)
expect(session.server_sequence).to_equal(TLS_MAX_SEQUENCE_V1)
expect(session.status).to_equal(DbdTlsSessionStatusV1.Failed)
expect(session.server_key.key.len()).to_equal(0u64)
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

- Canonical SPipe generation for source `3d36da70cfb81610f185a23c0fec4c26b1730e5782565b20cb075f4fc8715d30`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3d36da70cfb81610f185a23c0fec4c26b1730e5782565b20cb075f4fc8715d30`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3d36da70cfb81610f185a23c0fec4c26b1730e5782565b20cb075f4fc8715d30`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/apps/dbd/dbd_tls_spec.spl
mirror: doc/06_spec/01_unit/os/apps/dbd/dbd_tls_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/dbd/dbd_tls_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/dbd/dbd_tls_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/dbd/dbd_tls_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mutates one session owner across one-byte ingress with bounded work' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/dbd/dbd_tls_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains split ciphertext and releases plaintext only after authentication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/dbd/dbd_tls_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'authenticates coalesced records and commits each sequence in order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
