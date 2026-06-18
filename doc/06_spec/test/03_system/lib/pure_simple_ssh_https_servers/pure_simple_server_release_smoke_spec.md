# Pure Simple Server Release Smoke Specification

> <details>

<!-- sdn-diagram:id=pure_simple_server_release_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pure_simple_server_release_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pure_simple_server_release_smoke_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pure_simple_server_release_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Simple Server Release Smoke Specification

## Scenarios

### pure Simple SSH and HTTPS server release smoke

#### runs release preflight, release plans, success and failure paths without native protocol bypass

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = rt_process_run("bin/simple", ["run", "src/app/test/pure_simple_server_release_smoke.spl"])
expect(code).to_equal(0)
expect(stderr).to_equal("")
expect(stdout).to_contain("hosted-linux ssh release-preflight ready=true simple_protocol=true adapter=hosted-linux-rt-host-access")
expect(stdout).to_contain("hosted-linux https release-preflight ready=true simple_protocol=true adapter=hosted-linux-rt-host-access")
expect(stdout).to_contain("simpleos ssh release-preflight ready=true simple_protocol=true adapter=simpleos-kernel-host-access")
expect(stdout).to_contain("simpleos https release-preflight ready=true simple_protocol=true adapter=simpleos-kernel-host-access")
expect(stdout).to_contain("hosted-linux ssh release-plan ready=true simple_protocol=true adapter=hosted-linux-rt-host-access version=simple-ssh-version-exchange kex=simple-ssh-kex auth=simple-ssh-auth channel=simple-ssh-channel command=simple-host-process-exec")
expect(stdout).to_contain("simpleos ssh release-plan ready=true simple_protocol=true adapter=simpleos-kernel-host-access version=simple-ssh-version-exchange kex=simple-ssh-kex auth=simple-ssh-auth channel=simple-ssh-channel command=simple-host-process-exec")
expect(stdout).to_contain("hosted-linux https release-plan ready=true simple_protocol=true adapter=hosted-linux-rt-host-access tls=simple-tls12-server http=simple-http-response")
expect(stdout).to_contain("simpleos https release-plan ready=true simple_protocol=true adapter=simpleos-kernel-host-access tls=simple-tls12-server http=simple-http-response")
expect(stdout).to_contain("hosted-linux ssh mode-check mode=alpha simple_protocol=true allows_native_protocol_bypass=true")
expect(stdout).to_contain("hosted-linux ssh mode-check mode=beta simple_protocol=true allows_native_protocol_bypass=true")
expect(stdout).to_contain("hosted-linux ssh mode-check mode=release simple_protocol=true allows_native_protocol_bypass=false")
expect(stdout).to_contain("ssh native-bypass release-blocked=true reason=ssh release adapter cannot use native protocol bypass")
expect(stdout).to_contain("https native-bypass release-blocked=true reason=https release adapter cannot use native protocol bypass")
expect(stdout).to_contain("ssh success-auth simple_protocol=true accepted=true method=password user=root")
expect(stdout).to_contain("ssh failed-auth simple_protocol=true rejected=true method=password")
expect(stdout).to_contain("ssh channel-exec simple_protocol=true parsed=true launchable=true request=exec command=simple path=/usr/bin/simple")
expect(stdout).to_contain("https success-response simple_protocol=true accepted=true status=200 body=release-smoke")
expect(stdout).to_contain("https application-data simple_protocol=true encrypted=true decrypted=true content_type=23")
expect(stdout).to_contain("https request-route simple_protocol=true parsed=true routed=true method=GET path=/release-smoke handler=release-smoke")
expect(stdout).to_contain("https failed-handshake simple_protocol=true rejected=true reason=tls record version unsupported")
expect(stdout).to_contain("status=pass")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/03_system/lib/pure_simple_ssh_https_servers/pure_simple_server_release_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- pure Simple SSH and HTTPS server release smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
