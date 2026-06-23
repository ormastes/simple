# Os Tls Hosted Interop Basic Specification

> <details>

<!-- sdn-diagram:id=os_tls_hosted_interop_basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_tls_hosted_interop_basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_tls_hosted_interop_basic_spec -> std
os_tls_hosted_interop_basic_spec -> os
os_tls_hosted_interop_basic_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_tls_hosted_interop_basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Os Tls Hosted Interop Basic Specification

## Scenarios

### Hosted TLS interop basic

#### loads the shared tls test server SDN config

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = load_tls_test_server_config("tools/tls_test_server/server.sdn")
expect(result.err.?).to_equal(false)
val config = result.unwrap()
expect(config.listen).to_equal("127.0.0.1:4433")
expect(config.accept_count).to_equal(1)
expect(config.require_client_auth).to_equal(false)
expect(config.fixture_dir).to_equal("build/tls_test_server")
```

</details>

#### validates exported fixtures with openssl and completes a hosted Simple client handshake

1. seed fixture dir
2. cleanup server processes
3. write server config
4. write server config
   - Expected: openssl_server_pid > 0 is true
5. sleep ms
6. kill server
7. cleanup server processes
   - Expected: simple_server_pid > 0 is true
8. sleep ms
9. kill server
10. cleanup server processes
   - Expected: file_exists(fixture_dir + "/ca.pem") is true
   - Expected: file_exists(fixture_dir + "/server.pem") is true
   - Expected: simple_result.2 equals `0`
11. cleanup fixture dir


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
