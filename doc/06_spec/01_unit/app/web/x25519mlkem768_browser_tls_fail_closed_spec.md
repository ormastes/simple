# X25519mlkem768 Browser Tls Fail Closed Specification

> Tests covering X25519MLKEM768 browser TLS fail-closed policy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Browser Tls Fail Closed Specification

## Scenarios

### X25519MLKEM768 browser TLS fail-closed policy

#### should REQ-017 rejects disabled certificate verification before transport

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should REQ-017 rejects disabled certificate verification before transport
- Reject an insecure browser certificate-verification configuration


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should REQ-017 rejects disabled certificate verification before transport")
step("Reject an insecure browser certificate-verification configuration")
val logger = Logger.new("pqc-policy", BrowserLogLevel.Error)
var manager = TlsManager.new(
    logger, _browser_tls_config(TlsVersion.Tls13, false))
match manager.handshake_address(
    "192.0.2.1", "example.test", 443, 100
):
    case Ok(_): fail("browser accepted disabled peer verification")
    case Err(error):
        expect(error.message).to_equal(
            "TLS peer verification cannot be disabled for browser connections")
```

</details>

#### should REQ-017 rejects an empty service identity before transport

- should REQ-017 rejects an empty service identity before transport
- Reject browser TLS without a certificate service identity
   - Expected: error.message equals `TLS handshake: empty hostname`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should REQ-017 rejects an empty service identity before transport")
step("Reject browser TLS without a certificate service identity")
val logger = Logger.new("pqc-policy", BrowserLogLevel.Error)
var manager = TlsManager.new(
    logger, _browser_tls_config(TlsVersion.Tls13, true))
match manager.handshake_address("192.0.2.1", "", 443, 100):
    case Ok(_): fail("browser accepted an empty certificate identity")
    case Err(error):
        expect(error.message).to_equal("TLS handshake: empty hostname")
```

</details>

#### should NFR-018 rejects invalid ports and expired deadlines before transport

- should NFR-018 rejects invalid ports and expired deadlines before transport
- Validate transport bounds before opening a socket
   - Expected: error.message equals `TLS handshake: invalid port 0`
   - Expected: error.message equals `TLS handshake: deadline exceeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should NFR-018 rejects invalid ports and expired deadlines before transport")
step("Validate transport bounds before opening a socket")
val logger = Logger.new("pqc-policy", BrowserLogLevel.Error)
var manager = TlsManager.new(
    logger, _browser_tls_config(TlsVersion.Tls13, true))
match manager.handshake_address(
    "192.0.2.1", "example.test", 0, 100
):
    case Ok(_): fail("browser accepted an invalid port")
    case Err(error):
        expect(error.message).to_equal("TLS handshake: invalid port 0")
match manager.handshake_address(
    "192.0.2.1", "example.test", 443, 0
):
    case Ok(_): fail("browser accepted an expired deadline")
    case Err(error):
        expect(error.message).to_equal("TLS handshake: deadline exceeded")
```

</details>

#### should REQ-017 rejects TLS 1.2 on the pure-Simple hybrid browser path

- should REQ-017 rejects TLS 1.2 on the pure-Simple hybrid browser path
- Require TLS 1.3 for the hybrid browser connection


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should REQ-017 rejects TLS 1.2 on the pure-Simple hybrid browser path")
step("Require TLS 1.3 for the hybrid browser connection")
val logger = Logger.new("pqc-policy", BrowserLogLevel.Error)
var manager = TlsManager.new(
    logger,
    _browser_tls_config(TlsVersion.Tls12, true)
)
match manager.handshake_address(
    "192.0.2.1", "example.test", 443, 100
):
    case Ok(_): fail("hybrid browser path accepted TLS 1.2")
    case Err(error):
        expect(error.message).to_equal(
            "Pure-Simple browser HTTPS requires a TLS 1.3 minimum")
```

</details>

#### should NFR-018 preserve pure-Simple trust anchoring expectations

- should NFR-018 preserve pure-Simple trust anchoring expectations
- Verify default trust-anchor enforcement remains explicit


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should NFR-018 preserve pure-Simple trust anchoring expectations")
step("Verify default trust-anchor enforcement remains explicit")
val logger = Logger.new("pqc-policy", BrowserLogLevel.Error)
var manager = TlsManager.new(
    logger, _browser_tls_config(TlsVersion.Tls13, true))
val handshake = manager.handshake_address(
    "192.0.2.1", "example.test", 443, 100
)
match handshake:
    case Ok(_): fail("browser should fail because test host is unreachable, not succeed")
    case Err(error):
        expect(error.message).to_start_with("TLS handshake failed for")
```

</details>

#### should NFR-018 preserve one absolute deadline through TCP and TLS

- should NFR-018 preserve one absolute deadline through TCP and TLS
- Bind the HTTP deadline to deadline-aware TLS record I/O


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should NFR-018 preserve one absolute deadline through TCP and TLS")
step("Bind the HTTP deadline to deadline-aware TLS record I/O")
val h1 = file_read(
    "src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl")
val browser_tls = file_read(
    "src/lib/gc_async_mut/gpu/browser_engine/net/tls.spl")
val tls_io = file_read("src/os/tls13/_Tls13/context_io.spl")
val tls_connect = file_read("src/os/tls13/_Tls13/psk_connect.spl")

expect(h1).to_contain("me request(req: FetchRequest, deadline_ms: i64 = 0)")
expect(h1).to_contain("val request_deadline_ms = if deadline_ms > 0")
expect(h1).to_contain("h1_deadline_remaining_ms(")
expect(h1).to_contain("rt_io_tcp_connect_timeout(connect_addr, remaining)")
expect(h1).to_contain("read_tcp_response_bytes(conn.tcp_fd, deadline_ms)")
expect(h1).to_contain("conn.read_text_timeout(8192, remaining)")
expect(browser_tls).to_contain("if timeout_ms <= 0")
expect(browser_tls).to_contain("browser_tls_connect_address(")
expect(browser_tls).to_contain("browser_tls_connect(host, port, host)")
expect(tls_connect).to_contain("fn tls13_connect_with_config")
expect(tls_io).to_contain("fn _io_send(io: Tls13Io")
```

</details>

#### should NFR-018 keep server read and write timeout owners distinct

- should NFR-018 keep server read and write timeout owners distinct
- Use the configured write timeout on the hybrid accept path


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should NFR-018 keep server read and write timeout owners distinct")
step("Use the configured write timeout on the hybrid accept path")
val worker = file_read(
    "src/lib/nogc_async_mut/http_server/worker.spl")
val tls_handshake = file_read("src/lib/nogc_async_mut/io/tls_handshake.spl")
val accept_start = worker.index_of("me handle_tls_accept")
val accept_end = worker.index_of("me handle_completion")
val accept_path = worker.slice(accept_start, accept_end)

expect(accept_path).to_contain("var cfg = self.tls_config")
expect(accept_path).to_contain("perform_server_handshake(")
expect(tls_handshake).to_contain("fn perform_server_handshake")
expect(tls_handshake).to_contain("read_tls_record(driver, fd)")
expect(tls_handshake).to_contain("send_all(driver, fd,")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/web/x25519mlkem768_browser_tls_fail_closed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 browser TLS fail-closed policy.
- X25519MLKEM768 browser TLS fail-closed policy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-017`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cfc8d21f28204bb225f5bbe729c8e1bb79c1518e08f1ec846f6f0a5e8f0c898a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cfc8d21f28204bb225f5bbe729c8e1bb79c1518e08f1ec846f6f0a5e8f0c898a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cfc8d21f28204bb225f5bbe729c8e1bb79c1518e08f1ec846f6f0a5e8f0c898a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/web/x25519mlkem768_browser_tls_fail_closed_spec.spl
mirror: doc/06_spec/01_unit/app/web/x25519mlkem768_browser_tls_fail_closed_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/web/x25519mlkem768_browser_tls_fail_closed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/web/x25519mlkem768_browser_tls_fail_closed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/web/x25519mlkem768_browser_tls_fail_closed_spec.spl:35:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should REQ-017 rejects disabled certificate verification before transport' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/web/x25519mlkem768_browser_tls_fail_closed_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should REQ-017 rejects disabled certificate verification before transport' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/web/x25519mlkem768_browser_tls_fail_closed_spec.spl:50:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should REQ-017 rejects an empty service identity before transport' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/web/x25519mlkem768_browser_tls_fail_closed_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should REQ-017 rejects an empty service identity before transport' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/web/x25519mlkem768_browser_tls_fail_closed_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should NFR-018 rejects invalid ports and expired deadlines before transport' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/web/x25519mlkem768_browser_tls_fail_closed_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should NFR-018 rejects invalid ports and expired deadlines before transport' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/web/x25519mlkem768_browser_tls_fail_closed_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should REQ-017 rejects TLS 1.2 on the pure-Simple hybrid browser path' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/web/x25519mlkem768_browser_tls_fail_closed_spec.spl:99:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should NFR-018 preserve pure-Simple trust anchoring expectations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/web/x25519mlkem768_browser_tls_fail_closed_spec.spl:114:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should NFR-018 preserve one absolute deadline through TCP and TLS' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
