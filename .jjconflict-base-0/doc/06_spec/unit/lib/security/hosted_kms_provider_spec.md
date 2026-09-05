# Hosted Kms Provider Specification

> Tests covering hosted KMS key provider.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted Kms Provider Specification

## Scenarios

### hosted KMS key provider

#### builds outbound requests with bearer auth and TLS profile

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds outbound requests with bearer auth and TLS profile
   - Expected: request.method equals `POST`
   - Expected: request.url equals `https://kms.internal/simple/sign`
   - Expected: request.headers["authorization"] equals `Bearer transport-token`
   - Expected: request.tls_profile equals `mtls:kms-client`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds outbound requests with bearer auth and TLS profile")
var config = hosted_kms_default_config("https://kms.internal/simple")
config.bearer_token = "transport-token"
config.tls_profile = "mtls:kms-client"
var kms = HostedKmsKeyProvider.with_active_key(config, "key-1", "kms://cluster/key-1")

val request = kms.sign_request("key-1", "payload-1")

expect(request.method).to_equal("POST")
expect(request.url).to_equal("https://kms.internal/simple/sign")
expect(request.headers["authorization"]).to_equal("Bearer transport-token")
expect(request.tls_profile).to_equal("mtls:kms-client")
expect(request.body).to_contain("\"key_handle\":\"kms://cluster/key-1\"")
```

</details>

#### refuses unknown keys without contacting transport

- refuses unknown keys without contacting transport
   - Expected: kms.sign_payload("missing-key", "payload-1") equals ``
   - Expected: kms.verify_external_signature("missing-key", "payload-1", "sig") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses unknown keys without contacting transport")
var kms = HostedKmsKeyProvider.with_active_key(hosted_kms_default_config("https://kms.internal/simple"), "key-1", "kms://cluster/key-1")

expect(kms.sign_payload("missing-key", "payload-1")).to_equal("")
expect(kms.verify_external_signature("missing-key", "payload-1", "sig")).to_equal(false)
```

</details>

#### keeps live runtime HTTP transport explicitly opt-in

- keeps live runtime HTTP transport explicitly opt-in
   - Expected: hosted_kms_runtime_http_enabled(default_config) is false
   - Expected: hosted_kms_runtime_http_enabled(live_config) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps live runtime HTTP transport explicitly opt-in")
val default_config = hosted_kms_default_config("https://kms.internal/simple")
val live_config = hosted_kms_runtime_http_config("https://kms.internal/simple")

expect(hosted_kms_runtime_http_enabled(default_config)).to_equal(false)
expect(hosted_kms_runtime_http_enabled(live_config)).to_equal(true)
```

</details>

#### converts hosted KMS headers to runtime HTTP header lines

- converts hosted KMS headers to runtime HTTP header lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts hosted KMS headers to runtime HTTP header lines")
val request = HostedKmsKeyProvider.with_active_key(hosted_kms_default_config("https://kms.internal/simple"), "key-1", "kms://cluster/key-1").sign_request("key-1", "payload-1")
val lines = hosted_kms_headers_for_runtime(request.headers)

expect(lines.join("\n")).to_contain("content-type: application/json")
expect(lines.join("\n")).to_contain("x-simple-kms-vendor: generic-http-kms")
```

</details>

#### signs with an external KMS response

- signs with an external KMS response
   - Expected: kms.sign_payload("key-1", "payload-1") equals `external-sig`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("signs with an external KMS response")
var kms = HostedKmsKeyProvider.with_active_key(hosted_kms_default_config("https://kms.internal/simple"), "key-1", "kms://cluster/key-1")
val request = kms.sign_request("key-1", "payload-1")
kms.register_response(request, HostedKmsHttpResponse(status_code: 200, body: "{\"signature\":\"external-sig\"}", error: ""))

expect(kms.sign_payload("key-1", "payload-1")).to_equal("external-sig")
```

</details>

#### fails closed on malformed or rejected KMS responses

- fails closed on malformed or rejected KMS responses
   - Expected: kms.sign_payload("key-1", "payload-1") equals ``
   - Expected: kms.verify_external_signature("key-1", "payload-1", "sig") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on malformed or rejected KMS responses")
var kms = HostedKmsKeyProvider.with_active_key(hosted_kms_default_config("https://kms.internal/simple"), "key-1", "kms://cluster/key-1")
val malformed = kms.sign_request("key-1", "payload-1")
kms.register_response(malformed, HostedKmsHttpResponse(status_code: 200, body: "{\"ok\":true}", error: ""))
val rejected = kms.verify_request("key-1", "payload-1", "sig")
kms.register_response(rejected, HostedKmsHttpResponse(status_code: 503, body: "{\"valid\":true}", error: ""))

expect(kms.sign_payload("key-1", "payload-1")).to_equal("")
expect(kms.verify_external_signature("key-1", "payload-1", "sig")).to_equal(false)
```

</details>

#### validates remote SecurityContext through the existing adapter seam

- validates remote SecurityContext through the existing adapter seam
   - Expected: ctx.is_authenticated() is true
   - Expected: ctx.has_capability("billing.write") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates remote SecurityContext through the existing adapter seam")
var sessions = RemoteSecuritySessionStoreAdapter.replicated("redis", "security:kms")
sessions.create_session("kms-session", "user-14", ["billing.read", "billing.write"], 9000)
var kms = HostedKmsKeyProvider.with_active_key(hosted_kms_default_config("https://kms.internal/simple"), "key-1", "kms://cluster/key-1")
val payload = remote_security_token_payload_v2("key-1", "kms-session", "user-14", 8000, ["billing.read"])
val sign_request = kms.sign_request("key-1", payload)
kms.register_response(sign_request, HostedKmsHttpResponse(status_code: 200, body: "{\"signature\":\"external-sig\"}", error: ""))
val request = kms.verify_request("key-1", payload, "external-sig")
kms.register_response(request, HostedKmsHttpResponse(status_code: 200, body: "{\"valid\":true}", error: ""))
val token = kms.token_with_kms_signature("key-1", "kms-session", "user-14", 8000, ["billing.read"])
val provider = kms.rollout_provider_for_verified_signature("key-1", payload, "external-sig")
val ctx = validate_remote_security_context_with_adapters(bearer_headers(token), "198.51.100.50", "kms-session", provider, sessions, 2000)

expect(token).to_contain("simple-v2|key-1|kms-session")
expect(ctx.is_authenticated()).to_equal(true)
expect(ctx.has_capability("billing.write")).to_equal(true)
```

</details>

#### exports only opaque key handles, not raw signing keys

- exports only opaque key handles, not raw signing keys
   - Expected: sdn does not contain `signing_key`
   - Expected: sdn does not contain `raw`
   - Expected: sdn does not contain `AWS_SECRET_ACCESS_KEY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports only opaque key handles, not raw signing keys")
var kms = HostedKmsKeyProvider.with_active_key(hosted_kms_default_config("https://kms.internal/simple"), "key-1", "hsm://slot/key-1")
val sdn = kms.export_sdn()

expect(sdn).to_contain("key_handle|key-1|hsm://slot/key-1")
expect(sdn.contains("signing_key")).to_equal(false)
expect(sdn.contains("raw")).to_equal(false)
expect(sdn.contains("AWS_SECRET_ACCESS_KEY")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/security/hosted_kms_provider_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering hosted KMS key provider.
- hosted KMS key provider

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `c043583dd7cb72bfc32715572bd1e0b95838f55b16599f5bf4e68007ec603341`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c043583dd7cb72bfc32715572bd1e0b95838f55b16599f5bf4e68007ec603341`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c043583dd7cb72bfc32715572bd1e0b95838f55b16599f5bf4e68007ec603341`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/security/hosted_kms_provider_spec.spl
mirror: doc/06_spec/unit/lib/security/hosted_kms_provider_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/security/hosted_kms_provider_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/security/hosted_kms_provider_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/security/hosted_kms_provider_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds outbound requests with bearer auth and TLS profile' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/security/hosted_kms_provider_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses unknown keys without contacting transport' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/security/hosted_kms_provider_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps live runtime HTTP transport explicitly opt-in' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
