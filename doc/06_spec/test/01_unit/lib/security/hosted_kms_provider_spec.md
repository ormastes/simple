# Hosted Kms Provider Specification

> 1. var config = hosted kms default config

<!-- sdn-diagram:id=hosted_kms_provider_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hosted_kms_provider_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hosted_kms_provider_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hosted_kms_provider_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted Kms Provider Specification

## Scenarios

### hosted KMS key provider

#### builds outbound requests with bearer auth and TLS profile

1. var config = hosted kms default config
2. var kms = HostedKmsKeyProvider with active key
   - Expected: request.method equals `POST`
   - Expected: request.url equals `https://kms.internal/simple/sign`
   - Expected: request.headers["authorization"] equals `Bearer transport-token`
   - Expected: request.tls_profile equals `mtls:kms-client`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var kms = HostedKmsKeyProvider with active key
   - Expected: kms.sign_payload("missing-key", "payload-1") equals ``
   - Expected: kms.verify_external_signature("missing-key", "payload-1", "sig") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var kms = HostedKmsKeyProvider.with_active_key(hosted_kms_default_config("https://kms.internal/simple"), "key-1", "kms://cluster/key-1")

expect(kms.sign_payload("missing-key", "payload-1")).to_equal("")
expect(kms.verify_external_signature("missing-key", "payload-1", "sig")).to_equal(false)
```

</details>

#### keeps live runtime HTTP transport explicitly opt-in

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_config = hosted_kms_default_config("https://kms.internal/simple")
val live_config = hosted_kms_runtime_http_config("https://kms.internal/simple")

expect(hosted_kms_runtime_http_enabled(default_config)).to_equal(false)
expect(hosted_kms_runtime_http_enabled(live_config)).to_equal(true)
```

</details>

#### converts hosted KMS headers to runtime HTTP header lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = HostedKmsKeyProvider.with_active_key(hosted_kms_default_config("https://kms.internal/simple"), "key-1", "kms://cluster/key-1").sign_request("key-1", "payload-1")
val lines = hosted_kms_headers_for_runtime(request.headers)

expect(lines.join("\n")).to_contain("content-type: application/json")
expect(lines.join("\n")).to_contain("x-simple-kms-vendor: generic-http-kms")
```

</details>

#### signs with an external KMS response

1. var kms = HostedKmsKeyProvider with active key
2. kms register response
   - Expected: kms.sign_payload("key-1", "payload-1") equals `external-sig`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var kms = HostedKmsKeyProvider.with_active_key(hosted_kms_default_config("https://kms.internal/simple"), "key-1", "kms://cluster/key-1")
val request = kms.sign_request("key-1", "payload-1")
kms.register_response(request, HostedKmsHttpResponse(status_code: 200, body: "{\"signature\":\"external-sig\"}", error: ""))

expect(kms.sign_payload("key-1", "payload-1")).to_equal("external-sig")
```

</details>

#### fails closed on malformed or rejected KMS responses

1. var kms = HostedKmsKeyProvider with active key
2. kms register response
3. kms register response
   - Expected: kms.sign_payload("key-1", "payload-1") equals ``
   - Expected: kms.verify_external_signature("key-1", "payload-1", "sig") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var sessions = RemoteSecuritySessionStoreAdapter replicated
2. sessions create session
3. var kms = HostedKmsKeyProvider with active key
4. kms register response
5. kms register response
   - Expected: ctx.is_authenticated() is true
   - Expected: ctx.has_capability("billing.write") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var kms = HostedKmsKeyProvider with active key
   - Expected: sdn does not contain `signing_key`
   - Expected: sdn does not contain `raw`
   - Expected: sdn does not contain `AWS_SECRET_ACCESS_KEY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/lib/security/hosted_kms_provider_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
