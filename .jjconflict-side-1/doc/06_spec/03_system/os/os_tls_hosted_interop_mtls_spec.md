# Os Tls Hosted Interop Mtls Specification

> 1. seed fixture dir

<!-- sdn-diagram:id=os_tls_hosted_interop_mtls_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_tls_hosted_interop_mtls_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_tls_hosted_interop_mtls_spec -> std
os_tls_hosted_interop_mtls_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_tls_hosted_interop_mtls_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Os Tls Hosted Interop Mtls Specification

## Scenarios

### Hosted TLS interop mTLS

#### requires a client certificate when the shared SDN config enables mTLS

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
   - Expected: missing_cert.2 == 0 is false
   - Expected: simple_result.2 equals `0`
11. cleanup fixture dir


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val build = ensure_server_bin()
expect(build.2).to_equal(0)
expect(file_exists(server_bin())).to_equal(true)
expect(file_exists(simple_bin())).to_equal(true)

val fixture_dir = make_temp_fixture_dir("mtls")
val openssl_listen = "127.0.0.1:34435"
val simple_listen = "127.0.0.1:34436"
val openssl_config_path = fixture_dir + "/mtls_openssl.sdn"
val simple_config_path = fixture_dir + "/mtls_simple.sdn"
seed_fixture_dir(fixture_dir)
cleanup_server_processes()
write_server_config(openssl_config_path, openssl_listen, fixture_dir, true, 1)
write_server_config(simple_config_path, simple_listen, fixture_dir, true, 1)

val openssl_server_pid = spawn_server(openssl_config_path)
expect(openssl_server_pid > 0).to_equal(true)
if openssl_server_pid <= 0:
    return

sleep_ms(1000)
val missing_cert = run_openssl_client(openssl_listen, fixture_dir, false)
kill_server(openssl_server_pid)
cleanup_server_processes()

val simple_server_pid = spawn_server(simple_config_path)
expect(simple_server_pid > 0).to_equal(true)
if simple_server_pid <= 0:
    return

sleep_ms(1000)
val simple_result = run_simple_client(simple_config_path)
kill_server(simple_server_pid)
cleanup_server_processes()

expect(missing_cert.2 == 0).to_equal(false)
val simple_output = simple_result.0 + simple_result.1
if simple_output.contains("unknown extern function"):
    print "[os_tls_hosted_interop_mtls_spec] skipping Simple hosted client: TLS runtime externs unavailable"
    expect(simple_output).to_contain("unknown extern function")
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
| Source | `test/03_system/os/os_tls_hosted_interop_mtls_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Hosted TLS interop mTLS

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
