# @req REQ-DNS-WIRE-QTYPE

> DNS QTYPE wire-encoding detection spec — every record type, not just AAAA.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @req REQ-DNS-WIRE-QTYPE

DNS QTYPE wire-encoding detection spec — every record type, not just AAAA.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/dns/dns_qtype_encoding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

DNS QTYPE wire-encoding detection spec — every record type, not just AAAA.

Audience: anyone changing `src/lib/nogc_sync_mut/dns/wire.spl`, or reading a
DNS query byte dump and deciding which two bytes are the QTYPE.

Why this spec exists: `dns_spec.spl`'s "AAAA query has QTYPE=28" example read
the QTYPE out of the LAST two bytes of the query. In RFC 1035 §4.1.2 a question
is QNAME, then QTYPE, then QCLASS — so the last two bytes are the QCLASS, and
that example was asserting `qclass_low == 28` against a correct encoder. It read
back `1` (IN) and was filed as a defect in the query builder
(`doc/08_tracking/bug/dns_aaaa_query_qtype_not_28_2026-08-17.md`).

The generalisation: an off-by-two QTYPE read is invisible for record type A,
because A=1 and CLASS_IN=1 are the same byte. It only shows up for a type whose
value differs from 1. So this spec pins the QTYPE offset AND the IANA value for
every record type the library declares — A=1, NS=2, CNAME=5, MX=15, TXT=16,
AAAA=28, SRV=33 — which is what makes it a class detector rather than a
one-record regression test.

## Scenarios

### DNS query QTYPE encoding, across every declared record type

#### places QTYPE immediately before QCLASS for all seven record types

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- places QTYPE immediately before QCLASS for all seven record types
- Encode one query per record type and inspect the question tail
   - Expected: qtype_tail_reason("A", DNS_TYPE_A) equals ``
   - Expected: qtype_tail_reason("NS", DNS_TYPE_NS) equals ``
   - Expected: qtype_tail_reason("CNAME", DNS_TYPE_CNAME) equals ``
   - Expected: qtype_tail_reason("MX", DNS_TYPE_MX) equals ``
   - Expected: qtype_tail_reason("TXT", DNS_TYPE_TXT) equals ``
   - Expected: qtype_tail_reason("AAAA", DNS_TYPE_AAAA) equals ``
   - Expected: qtype_tail_reason("SRV", DNS_TYPE_SRV) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("places QTYPE immediately before QCLASS for all seven record types")
"""A DNS client asks for each record type in turn and checks the bytes
it is about to put on the wire: the QTYPE it requested, followed by the
IN class. Any record type encoded at the wrong offset names itself."""

step("Encode one query per record type and inspect the question tail")
expect(qtype_tail_reason("A", DNS_TYPE_A)).to_equal("")
expect(qtype_tail_reason("NS", DNS_TYPE_NS)).to_equal("")
expect(qtype_tail_reason("CNAME", DNS_TYPE_CNAME)).to_equal("")
expect(qtype_tail_reason("MX", DNS_TYPE_MX)).to_equal("")
expect(qtype_tail_reason("TXT", DNS_TYPE_TXT)).to_equal("")
expect(qtype_tail_reason("AAAA", DNS_TYPE_AAAA)).to_equal("")
expect(qtype_tail_reason("SRV", DNS_TYPE_SRV)).to_equal("")
```

</details>

#### pins the IANA record-type numbers the encoder writes

- pins the IANA record-type numbers the encoder writes
- Compare each declared constant against its IANA assignment
   - Expected: DNS_TYPE_A equals `1`
   - Expected: DNS_TYPE_NS equals `2`
   - Expected: DNS_TYPE_CNAME equals `5`
   - Expected: DNS_TYPE_MX equals `15`
   - Expected: DNS_TYPE_TXT equals `16`
   - Expected: DNS_TYPE_AAAA equals `28`
   - Expected: DNS_TYPE_SRV equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pins the IANA record-type numbers the encoder writes")
"""The offsets above only matter if the constants themselves are the
registered values. These are IANA DNS RR TYPE assignments, not
implementation choices, so they are asserted directly."""

step("Compare each declared constant against its IANA assignment")
expect(DNS_TYPE_A).to_equal(1)
expect(DNS_TYPE_NS).to_equal(2)
expect(DNS_TYPE_CNAME).to_equal(5)
expect(DNS_TYPE_MX).to_equal(15)
expect(DNS_TYPE_TXT).to_equal(16)
expect(DNS_TYPE_AAAA).to_equal(28)
expect(DNS_TYPE_SRV).to_equal(33)
```

</details>

#### reads back QCLASS, not QTYPE, from the final two bytes

- reads back QCLASS, not QTYPE, from the final two bytes
- Encode an AAAA query and read its final two bytes
   - Expected: q[last] equals `1`
   - Expected: q[last - 1] equals `0`
- Read the QTYPE from the two bytes before that
   - Expected: q[last - 2] equals `28`
   - Expected: q[last - 3] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads back QCLASS, not QTYPE, from the final two bytes")
"""This is the exact confusion that produced the AAAA bug report. The
last two bytes of a query are always 0,1 — the IN class — no matter
which record type was requested. A reader that expects 0,28 there for
an AAAA query is reading the wrong field, and this example says so."""

step("Encode an AAAA query and read its final two bytes")
val q = dns_wire_encode_query(1, "example.com", DNS_TYPE_AAAA)
val last = q.length() - 1
expect(q[last]).to_equal(1)
expect(q[last - 1]).to_equal(0)

step("Read the QTYPE from the two bytes before that")
expect(q[last - 2]).to_equal(28)
expect(q[last - 3]).to_equal(0)
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

- `REQ-SSPEC-LIB`
- `REQ-DNS-WIRE-QTYPE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `455889e0343327eb552756bdb986c0bf552c7052382b69214fc24c38437e9b6d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `455889e0343327eb552756bdb986c0bf552c7052382b69214fc24c38437e9b6d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `455889e0343327eb552756bdb986c0bf552c7052382b69214fc24c38437e9b6d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/dns/dns_qtype_encoding_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/dns/dns_qtype_encoding_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/dns/dns_qtype_encoding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/dns/dns_qtype_encoding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/dns/dns_qtype_encoding_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/dns/dns_qtype_encoding_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'places QTYPE immediately before QCLASS for all seven record types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/dns/dns_qtype_encoding_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pins the IANA record-type numbers the encoder writes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/dns/dns_qtype_encoding_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads back QCLASS, not QTYPE, from the final two bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
