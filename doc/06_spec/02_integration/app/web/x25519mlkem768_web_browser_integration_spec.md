# X25519mlkem768 Web Browser Integration Specification

> Tests covering hybrid TLS web adapter contract (no hosted socket), live Simple browser to SimpleServer hybrid TLS.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Web Browser Integration Specification

## Scenarios

### hybrid TLS web adapter contract (no hosted socket)

#### should REQ-017 accepts only the Ed25519 certificate algorithm for server phase one

- Classify the server certificate signature algorithm


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Classify the server certificate signature algorithm")
expect(tls_certificate_oid_is_ed25519([1, 3, 101, 112])).to_be(true)
expect(tls_certificate_oid_is_ed25519([1, 2, 840, 113549])).to_be(false)
expect(tls_certificate_oid_is_ed25519([])).to_be(false)
```

</details>

#### should REQ-017 NFR-018 preserves negotiated X25519MLKEM768 evidence in the web session

- Convert the accepted TLS context into the HTTP record session
   - Expected: session.named_group equals `GROUP_X25519_MLKEM768`
   - Expected: session.client_seq equals `0u64`
   - Expected: session.server_seq equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Convert the accepted TLS context into the HTTP record session")
val session = tls13_server_application_session(_web_context())
expect(session.named_group).to_equal(GROUP_X25519_MLKEM768)
expect(session.client_seq).to_equal(0u64)
expect(session.server_seq).to_equal(0u64)
```

</details>

#### should REQ-017 NFR-018 round-trips HTTP bytes through pure-Simple TLS 1.3 records

- Encrypt a browser request with the negotiated client key
- tls13 server application session
   - Expected: received.data equals `request`
   - Expected: received.session.client_seq equals `1u64`
- Encrypt the server response and decrypt it with the peer key
   - Expected: content_type equals `0x17`
   - Expected: plaintext equals `response`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Encrypt a browser request with the negotiated client key")
val key = RecordKey(key: _web_key(), iv: _web_iv())
val request = [71u8, 69u8, 84u8]
val request_record = record13_encrypt_for_suite(
    0x1301u16, key, 0u64, 0x17, request)
val received = tls13_server_receive(
    tls13_server_application_session(_web_context()), request_record)
expect(received.ok).to_be(true)
expect(received.data).to_equal(request)
expect(received.session.client_seq).to_equal(1u64)

step("Encrypt the server response and decrypt it with the peer key")
val response = [79u8, 75u8]
val sent = tls13_server_send(received.session, response)
match record13_decrypt_for_suite(
    0x1301u16, key, 0u64, sent.record
):
    case RecordResult.Ok(content_type, plaintext):
        expect(content_type).to_equal(0x17)
        expect(plaintext).to_equal(response)
    case RecordResult.Err(reason):
        fail("valid server application record rejected: {reason}")
```

</details>

#### should REQ-017 NFR-018 fails browser HTTPS closed without pure-Simple trust anchors

- Configure hybrid-first browser TLS without a trust store
- var manager = TlsManager new


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Configure hybrid-first browser TLS without a trust store")
val config = TlsConfig(
    min_version: TlsVersion.Tls13,
    verify_peer: true,
    sni_hostname: "",
    root_store: [],
    enable_x25519_mlkem768: true,
    require_x25519_mlkem768: false
)
val logger = Logger.new("pqc-browser-test", BrowserLogLevel.Error)
var manager = TlsManager.new(logger, config)
match manager.handshake_address(
    "127.0.0.1", "example.test", 443, 100
):
    case Ok(_): fail("browser connected without a trust anchor")
    case Err(error):
        expect(error.message).to_equal(
            "Pure-Simple browser TLS trust store is empty")
expect(tls13_browser_connect_address("::1", 443)).to_equal(
    "[::1]:443")
```

</details>

#### should REQ-017 NFR-018 uses bounded platform CA bundle discovery

- Discover only the bounded platform trust-store candidates
   - Expected: paths.len() equals `3`
   - Expected: paths[2] equals `/etc/ssl/cert.pem`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Discover only the bounded platform trust-store candidates")
val paths = browser_system_ca_bundle_paths()
expect(paths.len()).to_equal(3)
expect(paths[0]).to_end_with("ca-certificates.crt")
expect(paths[2]).to_equal("/etc/ssl/cert.pem")
```

</details>

### live Simple browser to SimpleServer hybrid TLS

#### should REQ-017 NFR-018 serve HTTP through a real X25519MLKEM768 socket

- Bind the production SimpleServer worker with an Ed25519 test identity
- var config = default server config
- 0, config, AsyncRouter new
- build default pipeline
- Ok
- Err
-  live hybrid workers remove
- fail
- Trust the fixture root and negotiate through the browser host-stream transport
- Ok
- Err
-  stop live hybrid worker
- fail
- root store: [rt text to bytes
- var manager = TlsManager new
- Ok
- Err
-  stop live hybrid worker
- fail
- Send HTTP over the negotiated session and read the encrypted server response
-  stop live hybrid worker


<details>
<summary>Executable SSpec</summary>

Runnable source: 75 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind the production SimpleServer worker with an Ed25519 test identity")
val fixture_root = "test/fixtures/crypto/x25519mlkem768"
val cert_path = "{fixture_root}/localhost_ed25519_cert.pem"
val live_port: i64 = 39000 + (getpid() % 1000)
var config = default_server_config()
config.listen_addr = "127.0.0.1:{live_port}"
config.worker_count = 1
config.read_timeout_ms = 5000
config.write_timeout_ms = 5000
config.idle_timeout_ms = 5000
config.tls_enabled = true
config.tls_cert_path = cert_path
config.tls_key_path = "{fixture_root}/localhost_ed25519_key.pem"
config.tls_min_version = "1.3"
config.locations = [LocationConfig(
    pattern: "/",
    match_type: "prefix",
    handler_type: "static",
    root: fixture_root,
    proxy_pass: "",
    middlewares: []
)]
val control = channel_new()
val worker_result = Worker.create(
    0, config, AsyncRouter.new(config.locations),
    build_default_pipeline(), create_default_registry(fixture_root),
    control
)
match worker_result:
    Ok(worker): _live_hybrid_workers[0] = worker
    Err(error): fail("live SimpleServer worker failed to bind: {error}")
val thread_handle = spl_thread_create(\: _run_live_hybrid_worker(0), 0)
if thread_handle <= 0:
    _live_hybrid_workers.remove(0)
    fail("live SimpleServer worker thread creation failed")
    return

step("Trust the fixture root and negotiate through the browser host-stream transport")
val chain = match TlsCertificateChain.from_pem_file(cert_path):
    Ok(value): value
    Err(reason):
        _stop_live_hybrid_worker(control, thread_handle)
        fail("fixture certificate failed to load: {reason}")
        return
val tls_config = TlsConfig(
    min_version: TlsVersion.Tls13,
    verify_peer: true,
    sni_hostname: "localhost",
    root_store: [rt_text_to_bytes(chain.leaf().raw_der)],
    enable_x25519_mlkem768: true,
    require_x25519_mlkem768: true
)
val logger = Logger.new("pqc-live-browser-test", BrowserLogLevel.Error)
var manager = TlsManager.new(logger, tls_config)
var connection = match manager.handshake_address(
    "127.0.0.1", "localhost", live_port, 5000
):
    Ok(value): value
    Err(error):
        _stop_live_hybrid_worker(control, thread_handle)
        fail("live hybrid browser handshake failed: {error.message}")
        return

step("Send HTTP over the negotiated session and read the encrypted server response")
expect(connection.negotiated_x25519_mlkem768()).to_be(true)
val written = connection.write_text_timeout(
    "GET /hello.txt HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n",
    5000
)
val response = connection.read_text_timeout(8192, 5000)
val _ = connection.close()
_stop_live_hybrid_worker(control, thread_handle)
expect(written).to_be_greater_than(0)
expect(response).to_start_with("HTTP/1.1 200")
expect(response).to_contain("simple browser over x25519mlkem768")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/web/x25519mlkem768_web_browser_integration_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering hybrid TLS web adapter contract (no hosted socket), live Simple browser to SimpleServer hybrid TLS.
- hybrid TLS web adapter contract (no hosted socket)
- live Simple browser to SimpleServer hybrid TLS

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
