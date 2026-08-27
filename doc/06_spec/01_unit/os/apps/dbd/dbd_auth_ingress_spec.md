# DBD mutable-byte AUTH ingress

> Exercises the byte-domain RESP AUTH owner used after authenticated TLS ingress.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DBD mutable-byte AUTH ingress

Exercises the byte-domain RESP AUTH owner used after authenticated TLS ingress.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/dbd/dbd_auth_ingress_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises the byte-domain RESP AUTH owner used after authenticated TLS ingress.
Credentials are constructed as mutable fixtures, never as immutable text.  The
scenarios cover split and coalesced requests, malformed framing, bounded
one-byte fragmentation, authentication success/failure/lockout, and owner-visible
zeroization on success, rejection, failure, and close.

## Scenarios

### DBD mutable AUTH framing

#### authenticates a request split across authenticated plaintext frames

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- authenticates a request split across authenticated plaintext frames
   - Expected: first equals `DbdAuthIngressStatusV1.NeedMore`
   - Expected: second equals `DbdAuthIngressStatusV1.NeedMore`
   - Expected: third equals `DbdAuthIngressStatusV1.Authenticated`
   - Expected: owner.identity() equals `operator`
   - Expected: owner.last_wiped_credential_byte_count() equals `32i64`
   - Expected: owner.retained_secret_byte_count() equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("authenticates a request split across authenticated plaintext frames")
val provider = _configured_provider(17u8)
val request = _auth_request(_credential(17u8))
val owner = DbdMutableAuthRequestOwnerV1.new(101)
val first = owner.ingest(provider, request.slice(0, 9))
expect(first).to_equal(DbdAuthIngressStatusV1.NeedMore)
val second = owner.ingest(provider, request.slice(9, 31))
expect(second).to_equal(DbdAuthIngressStatusV1.NeedMore)
val third = owner.ingest(
    provider, request.slice(31, request.len()))
expect(third).to_equal(DbdAuthIngressStatusV1.Authenticated)
expect(owner.can_dispatch()).to_be(true)
expect(owner.identity()).to_equal("operator")
expect(owner.last_credential_was_zeroized()).to_be(true)
expect(owner.last_wiped_credential_byte_count()).to_equal(32i64)
expect(owner.retained_secret_byte_count()).to_equal(0i64)
```

</details>

#### separates a coalesced post-auth command without treating it as secret

- separates a coalesced post-auth command without treating it as secret
   - Expected: status equals `DbdAuthIngressStatusV1.Authenticated`
   - Expected: owner.take_authenticated_trailing() equals `command`
   - Expected: owner.take_authenticated_trailing().len() equals `0u64`
   - Expected: owner.last_wiped_credential_byte_count() equals `32i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("separates a coalesced post-auth command without treating it as secret")
val provider = _configured_provider(19u8)
val command = "*1\r\n$4\r\nPING\r\n".bytes()
val owner = DbdMutableAuthRequestOwnerV1.new(102)
val status = owner.ingest(
    provider, _auth_request(_credential(19u8), command))
expect(status).to_equal(DbdAuthIngressStatusV1.Authenticated)
expect(owner.take_authenticated_trailing()).to_equal(command)
expect(owner.take_authenticated_trailing().len()).to_equal(0u64)
expect(owner.last_credential_was_zeroized()).to_be(true)
expect(owner.last_wiped_credential_byte_count()).to_equal(32i64)
```

</details>

#### rejects malformed AUTH syntax and wipes a collected credential prefix

- rejects malformed AUTH syntax and wipes a collected credential prefix
   - Expected: owner.last_wiped_credential_byte_count() equals `32i64`
   - Expected: owner.retained_secret_byte_count() equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed AUTH syntax and wipes a collected credential prefix")
val provider = _configured_provider(21u8)
var malformed = "*3\r\n$4\r\nAUTH\r\n$8\r\noperator\r\n$32\r\n".bytes()
var index: i64 = 0
while index < 32:
    malformed.push(21u8)
    index = index + 1
malformed.push(10u8)
val owner = DbdMutableAuthRequestOwnerV1.new(103)
expect(owner.ingest(provider, malformed)).to_equal(
    DbdAuthIngressStatusV1.Malformed)
expect(owner.can_dispatch()).to_be(false)
expect(owner.last_credential_was_zeroized()).to_be(true)
expect(owner.last_wiped_credential_byte_count()).to_equal(32i64)
expect(owner.retained_secret_byte_count()).to_equal(0i64)
expect(owner.ingest(provider, [1u8])).to_equal(
    DbdAuthIngressStatusV1.Closed)
```

</details>

#### accepts a legal AUTH request fragmented one plaintext byte at a time

- accepts a legal AUTH request fragmented one plaintext byte at a time
   - Expected: status equals `DbdAuthIngressStatusV1.NeedMore`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a legal AUTH request fragmented one plaintext byte at a time")
val provider = _configured_provider(23u8)
val request = _auth_request(_credential(23u8))
val owner = DbdMutableAuthRequestOwnerV1.new(104)
var fragment: i64 = 0
while fragment < request.len().to_i64() - 1:
    val status = owner.ingest(
        provider,
        request.slice(fragment.to_u64(), (fragment + 1).to_u64())
    )
    expect(status).to_equal(DbdAuthIngressStatusV1.NeedMore)
    fragment = fragment + 1
expect(owner.ingest(
    provider,
    request.slice(fragment.to_u64(), request.len())
)).to_equal(DbdAuthIngressStatusV1.Authenticated)
expect(owner.can_dispatch()).to_be(true)
expect(owner.last_credential_was_zeroized()).to_be(true)
```

</details>

### DBD mutable AUTH identity and lockout

#### wipes each rejected candidate and locks on the bounded fourth attempt

- wipes each rejected candidate and locks on the bounded fourth attempt
   - Expected: owner.retained_secret_byte_count() equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wipes each rejected candidate and locks on the bounded fourth attempt")
val provider = _configured_provider(29u8)
val wrong = _auth_request(_credential(30u8))
val owner = DbdMutableAuthRequestOwnerV1.new(105)
var attempt: i64 = 0
while attempt < DBD_MAX_AUTH_ATTEMPTS_PER_SESSION - 1:
    expect(owner.ingest(provider, wrong)).to_equal(
        DbdAuthIngressStatusV1.Rejected)
    expect(owner.last_credential_was_zeroized()).to_be(true)
    expect(owner.retained_secret_byte_count()).to_equal(0i64)
    attempt = attempt + 1
expect(owner.ingest(provider, wrong)).to_equal(
    DbdAuthIngressStatusV1.Locked)
expect(owner.is_locked()).to_be(true)
expect(owner.can_dispatch()).to_be(false)
expect(owner.attempt_count()).to_equal(
    DBD_MAX_AUTH_ATTEMPTS_PER_SESSION)
expect(owner.last_credential_was_zeroized()).to_be(true)
```

</details>

#### close wipes an incomplete credential held by the owner

- close wipes an incomplete credential held by the owner
   - Expected: owner.retained_secret_byte_count() equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("close wipes an incomplete credential held by the owner")
val provider = _configured_provider(31u8)
val request = _auth_request(_credential(31u8))
val owner = DbdMutableAuthRequestOwnerV1.new(106)
val partial = request.slice(0, request.len() - 10u64)
expect(owner.ingest(provider, partial)).to_equal(
    DbdAuthIngressStatusV1.NeedMore)
owner.close()
expect(owner.last_credential_was_zeroized()).to_be(true)
expect(owner.retained_secret_byte_count()).to_equal(0i64)
expect(owner.ingest(provider, [1u8])).to_equal(
    DbdAuthIngressStatusV1.Closed)
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

- Canonical SPipe generation for source `1aabd9276921176677aeb2de1418599ae4b913386f991edc40429e6684d9f8be`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1aabd9276921176677aeb2de1418599ae4b913386f991edc40429e6684d9f8be`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1aabd9276921176677aeb2de1418599ae4b913386f991edc40429e6684d9f8be`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/apps/dbd/dbd_auth_ingress_spec.spl
mirror: doc/06_spec/01_unit/os/apps/dbd/dbd_auth_ingress_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/dbd/dbd_auth_ingress_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/dbd/dbd_auth_ingress_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/dbd/dbd_auth_ingress_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'authenticates a request split across authenticated plaintext frames' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/dbd/dbd_auth_ingress_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'separates a coalesced post-auth command without treating it as secret' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/dbd/dbd_auth_ingress_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects malformed AUTH syntax and wipes a collected credential prefix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
