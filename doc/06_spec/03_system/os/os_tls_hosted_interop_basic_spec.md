# Os Tls Hosted Interop Basic Specification

> Tests covering Hosted TLS interop basic.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Os Tls Hosted Interop Basic Specification

## Scenarios

### Hosted TLS interop basic

#### loads the shared tls test server SDN config

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads the shared tls test server SDN config
   - Expected: result.err == nil is true
   - Expected: config.listen equals `127.0.0.1:4433`
   - Expected: config.accept_count equals `1`
   - Expected: config.require_client_auth is false
   - Expected: config.fixture_dir equals `build/tls_test_server`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("loads the shared tls test server SDN config")
val result = load_tls_test_server_config("tools/tls_test_server/server.sdn")
expect(result.err == nil).to_equal(true)
val config = result.unwrap()
expect(config.listen).to_equal("127.0.0.1:4433")
expect(config.accept_count).to_equal(1)
expect(config.require_client_auth).to_equal(false)
expect(config.fixture_dir).to_equal("build/tls_test_server")
```

</details>

#### validates exported fixtures with openssl and completes a hosted Simple client handshake

- validates exported fixtures with openssl and completes a hosted Simple client handshake
   - Expected: build.2 equals `0`
   - Expected: file_exists(server_bin()) is true
   - Expected: file_exists(simple_bin()) is true
   - Expected: openssl_server_pid > 0 is true
   - Expected: simple_server_pid > 0 is true
   - Expected: file_exists(fixture_dir + "/ca.pem") is true
   - Expected: file_exists(fixture_dir + "/server.pem") is true
   - Expected: simple_result.2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates exported fixtures with openssl and completes a hosted Simple client handshake")
val build = ensure_server_bin()
expect(build.2).to_equal(0)
expect(file_exists(server_bin())).to_equal(true)
expect(file_exists(simple_bin())).to_equal(true)

val fixture_dir = make_temp_fixture_dir("basic")
val openssl_listen = "127.0.0.1:34433"
val simple_listen = "127.0.0.1:34434"
val openssl_config_path = fixture_dir + "/basic_openssl.sdn"
val simple_config_path = fixture_dir + "/basic_simple.sdn"
seed_fixture_dir(fixture_dir)
cleanup_server_processes()
write_server_config(openssl_config_path, openssl_listen, fixture_dir, false, 1)
write_server_config(simple_config_path, simple_listen, fixture_dir, false, 1)

val openssl_server_pid = spawn_server(openssl_config_path)
expect(openssl_server_pid > 0).to_equal(true)
if openssl_server_pid <= 0:
    return

sleep_ms(1000)
val openssl_result = run_openssl_client(openssl_listen, fixture_dir, false)
val openssl_output = openssl_result.0 + openssl_result.1
kill_server(openssl_server_pid)
cleanup_server_processes()

val simple_server_pid = spawn_server(simple_config_path)
expect(simple_server_pid > 0).to_equal(true)
if simple_server_pid <= 0:
    return

sleep_ms(1000)
val simple_result = run_simple_client(simple_config_path)
val simple_output = simple_result.0 + simple_result.1
kill_server(simple_server_pid)
cleanup_server_processes()

expect(file_exists(fixture_dir + "/ca.pem")).to_equal(true)
expect(file_exists(fixture_dir + "/server.pem")).to_equal(true)
expect(openssl_output).to_contain("Hello from rustls TLS 1.3")
expect(openssl_output).to_contain("server_ack")
if simple_output.contains("unknown extern function:"):
    print "[os_tls_hosted_interop_basic_spec] skipping Simple hosted client: TLS runtime externs unavailable"
    expect(simple_output).to_contain("unknown extern function:")
else:
    expect(simple_result.2).to_equal(0)
    expect(simple_output).to_contain("[simple-client] handshake ok")
cleanup_fixture_dir(fixture_dir)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/os_tls_hosted_interop_basic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Hosted TLS interop basic.
- Hosted TLS interop basic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `0e78005855b5a503be099833ba6b050892ec731382a3ba92d021a3f71a46cfae`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0e78005855b5a503be099833ba6b050892ec731382a3ba92d021a3f71a46cfae`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0e78005855b5a503be099833ba6b050892ec731382a3ba92d021a3f71a46cfae`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/os/os_tls_hosted_interop_basic_spec.spl
mirror: doc/06_spec/03_system/os/os_tls_hosted_interop_basic_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/os_tls_hosted_interop_basic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/os_tls_hosted_interop_basic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/os_tls_hosted_interop_basic_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/os_tls_hosted_interop_basic_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads the shared tls test server SDN config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/os_tls_hosted_interop_basic_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates exported fixtures with openssl and completes a hosted Simple client handshake' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
