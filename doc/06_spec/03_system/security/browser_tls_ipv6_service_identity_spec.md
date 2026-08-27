# browser_tls_ipv6_service_identity_spec

> Bracketed IPv6 HTTPS authority and bare TLS service identity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# browser_tls_ipv6_service_identity_spec

Bracketed IPv6 HTTPS authority and bare TLS service identity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Security |
| Status | Active |
| Source | `test/03_system/security/browser_tls_ipv6_service_identity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Bracketed IPv6 HTTPS authority and bare TLS service identity.

This offline scenario exercises the canonical URL and H1 target preparation
without opening DNS, sockets, or a TLS provider. Live certificate-chain and
platform trust evidence remains a separate blocked gate.

## Scenarios

### Browser TLS IPv6 service identity

#### should separate IPv6 wire authority from the TLS peer identity

- should separate IPv6 wire authority from the TLS peer identity
   - Protocol capture: after_step
- Parse a bracketed IPv6 HTTPS authority
   - Protocol capture: after_step
   - Evidence: protocol response verified by 4 expected checks
   - Expected: url.scheme equals `https`
   - Expected: url.host equals `[2001:db8::1]`
   - Expected: url.port equals `8443`
   - Expected: url.authority() equals `[2001:db8::1]:8443`
- Select the bare numeric TLS service identity
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: identity equals `2001:db8::1`
- Reject malformed bracket forms from the literal fast path
   - Protocol capture: after_step
- Preserve bracketed authority on the HTTP wire
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should separate IPv6 wire authority from the TLS peer identity")
step("Parse a bracketed IPv6 HTTPS authority")
val url = Url.parse_or_opaque(
    "https://[2001:db8::1]:8443/resource?q=1"
)
expect(url.opaque).to_be(false)
expect(url.scheme).to_equal("https")
expect(url.host).to_equal("[2001:db8::1]")
expect(url.port).to_equal(8443)
expect(url.authority()).to_equal("[2001:db8::1]:8443")

step("Select the bare numeric TLS service identity")
val literal = h1_tls_ipv6_literal_identity(url.host)
if not literal.?:
    fail("canonical IPv6 URL host did not produce a TLS identity")
val identity = literal.unwrap()
expect(identity).to_equal("2001:db8::1")
expect(identity.contains("[")).to_be(false)
expect(identity.contains("]")).to_be(false)
expect(h1_tls_ipv6_literal_identity("secure.test")).to_be_nil()

step("Reject malformed bracket forms from the literal fast path")
expect(h1_tls_ipv6_literal_identity("[::1")).to_be_nil()
expect(h1_tls_ipv6_literal_identity("::1]")).to_be_nil()
expect(h1_tls_ipv6_literal_identity("[]")).to_be_nil()
expect(h1_tls_ipv6_literal_identity("[not-an-ip]")).to_be_nil()
expect(h1_tls_ipv6_literal_identity("[::::]")).to_be_nil()
expect(h1_tls_ipv6_literal_identity("[2001:db8:::1]")).to_be_nil()

step("Preserve bracketed authority on the HTTP wire")
val request = FetchRequest(
    method: "GET",
    url: url,
    headers: "Host: attacker.test\r\n",
    body: [],
    mode: RequestMode.SameOrigin,
    credentials: "omit"
)
val wire = build_request_bytes(request)
expect(wire).to_start_with(
    "GET /resource?q=1 HTTP/1.1\r\n" +
    "Host: [2001:db8::1]:8443\r\n"
)
expect(wire.contains("attacker.test")).to_be(false)
expect(wire).to_contain("\r\nConnection: close\r\n")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3455455c9e6d77bcdbfe1d044f1b68c5c4606274053de4552115bf8d5cd9a373`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3455455c9e6d77bcdbfe1d044f1b68c5c4606274053de4552115bf8d5cd9a373`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3455455c9e6d77bcdbfe1d044f1b68c5c4606274053de4552115bf8d5cd9a373`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/security/browser_tls_ipv6_service_identity_spec.spl
mirror: doc/06_spec/03_system/security/browser_tls_ipv6_service_identity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=95 oracle=90
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/security/browser_tls_ipv6_service_identity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/security/browser_tls_ipv6_service_identity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/security/browser_tls_ipv6_service_identity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/security/browser_tls_ipv6_service_identity_spec.spl:29:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should separate IPv6 wire authority from the TLS peer identity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/security/browser_tls_ipv6_service_identity_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should separate IPv6 wire authority from the TLS peer identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
