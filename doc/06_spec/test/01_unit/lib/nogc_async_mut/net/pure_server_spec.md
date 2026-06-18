# Pure Server Specification

> <details>

<!-- sdn-diagram:id=pure_server_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pure_server_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pure_server_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pure_server_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Server Specification

## Scenarios

### async pure server release routing policy

#### keeps SSH release mode on the Simple protocol path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = pure_server_release_route(PureServerProtocol.SSH, pure_server_hosted_linux_caps())
expect(route.is_ok()).to_be(true)
val decision = route.unwrap()
expect(decision.uses_simple_protocol).to_be(true)
expect(decision.allows_native_protocol_bypass).to_be(false)
```

</details>

#### keeps HTTPS release mode on the Simple protocol path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = pure_server_release_route(PureServerProtocol.HTTPS, pure_server_simpleos_caps())
expect(route.is_ok()).to_be(true)
val decision = route.unwrap()
expect(decision.uses_simple_protocol).to_be(true)
expect(decision.allows_native_protocol_bypass).to_be(false)
```

</details>

#### keeps comparison bypass out of release mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alpha = pure_server_route_decision(PureServerProtocol.HTTPS, PureServerMode.Alpha, pure_server_hosted_linux_caps()).unwrap()
val release = pure_server_route_decision(PureServerProtocol.HTTPS, PureServerMode.Release, pure_server_hosted_linux_caps()).unwrap()
expect(alpha.allows_native_protocol_bypass).to_be(true)
expect(release.allows_native_protocol_bypass).to_be(false)
```

</details>

#### fails closed when TCP read write is unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = PureServerHostAccessCaps(
    target: PureServerHostTarget.HostedLinux,
    can_accept_tcp: true,
    can_read_write_tcp: false,
    can_load_files: true,
    can_get_entropy: true,
    can_spawn_process: true
)
val route = pure_server_release_route(PureServerProtocol.HTTPS, caps)
expect(route.is_err()).to_be(true)
expect(route.err().unwrap()).to_equal("https requires tcp read/write host access")
```

</details>

#### hosted Linux and SimpleOS adapters satisfy async release routes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hosted = pure_server_release_route_for_adapter(PureServerProtocol.HTTPS, pure_server_hosted_linux_adapter())
val simpleos = pure_server_release_route_for_adapter(PureServerProtocol.SSH, pure_server_simpleos_adapter())
expect(hosted.is_ok()).to_be(true)
expect(simpleos.is_ok()).to_be(true)
expect(hosted.unwrap().allows_native_protocol_bypass).to_be(false)
```

</details>

#### rejects async adapters that use native protocol bypass in release mode

- caps: pure server hosted linux caps
   - Expected: route.err().unwrap() equals `https release adapter cannot use native protocol bypass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = PureServerHostAccessAdapter(
    name: "bad-native-tls-wrapper",
    target: PureServerHostTarget.HostedLinux,
    caps: pure_server_hosted_linux_caps(),
    uses_native_protocol_bypass: true,
    description: "bad"
)
val route = pure_server_release_route_for_adapter(PureServerProtocol.HTTPS, adapter)
expect(route.is_err()).to_be(true)
expect(route.err().unwrap()).to_equal("https release adapter cannot use native protocol bypass")
```

</details>

#### reports async hosted Linux preflights ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ssh = pure_server_hosted_linux_ssh_preflight()
val https = pure_server_hosted_linux_https_preflight()
expect(ssh.release_ready).to_be(true)
expect(https.release_ready).to_be(true)
expect(ssh.uses_simple_protocol).to_be(true)
```

</details>

#### reports async SimpleOS preflights ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ssh = pure_server_simpleos_ssh_preflight()
val https = pure_server_simpleos_https_preflight()
expect(ssh.release_ready).to_be(true)
expect(https.release_ready).to_be(true)
expect(https.adapter_name).to_equal("simpleos-kernel-host-access")
```

</details>

#### reports async failed preflight reason

- caps: pure server simpleos caps
   - Expected: preflight.reason equals `ssh release adapter cannot use native protocol bypass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = PureServerHostAccessAdapter(
    name: "bad-native-ssh-wrapper",
    target: PureServerHostTarget.SimpleOS,
    caps: pure_server_simpleos_caps(),
    uses_native_protocol_bypass: true,
    description: "bad"
)
val preflight = pure_server_release_preflight(PureServerProtocol.SSH, adapter)
expect(preflight.release_ready).to_be(false)
expect(preflight.reason).to_equal("ssh release adapter cannot use native protocol bypass")
```

</details>

#### builds async hosted Linux HTTPS release plan from Simple stages

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = pure_server_hosted_linux_https_release_plan("ok")
expect(plan.release_ready).to_be(true)
expect(plan.uses_simple_protocol).to_be(true)
expect(plan.adapter_name).to_equal("hosted-linux-rt-host-access")
expect(plan.tls_stage).to_equal("simple-tls12-server")
expect(plan.http_stage).to_equal("simple-http-response")
expect(plan.response_wire_preview).to_contain("HTTP/1.1 200 OK")
expect(plan.response_wire_preview).to_end_with("\r\n\r\nok")
```

</details>

#### builds async SimpleOS HTTPS release plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = pure_server_simpleos_https_release_plan("ready")
expect(plan.release_ready).to_be(true)
expect(plan.uses_simple_protocol).to_be(true)
expect(plan.adapter_name).to_equal("simpleos-kernel-host-access")
expect(plan.response_wire_preview).to_contain("Content-Length: 5")
```

</details>

#### blocks async HTTPS release plans for native bypass adapters

- caps: pure server hosted linux caps
   - Expected: plan.tls_stage equals `blocked`
   - Expected: plan.http_stage equals `blocked`
   - Expected: plan.reason equals `https release adapter cannot use native protocol bypass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = PureServerHostAccessAdapter(
    name: "rt-tls-server-wrapper",
    target: PureServerHostTarget.HostedLinux,
    caps: pure_server_hosted_linux_caps(),
    uses_native_protocol_bypass: true,
    description: "bad"
)
val plan = pure_server_https_release_plan(adapter, "nope")
expect(plan.release_ready).to_be(false)
expect(plan.uses_simple_protocol).to_be(false)
expect(plan.tls_stage).to_equal("blocked")
expect(plan.http_stage).to_equal("blocked")
expect(plan.reason).to_equal("https release adapter cannot use native protocol bypass")
```

</details>

#### builds async hosted Linux SSH release plan from Simple protocol stages

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = pure_server_hosted_linux_ssh_release_plan()
expect(plan.release_ready).to_be(true)
expect(plan.uses_simple_protocol).to_be(true)
expect(plan.adapter_name).to_equal("hosted-linux-rt-host-access")
expect(plan.version_exchange_stage).to_equal("simple-ssh-version-exchange")
expect(plan.kex_stage).to_equal("simple-ssh-kex")
expect(plan.auth_stage).to_equal("simple-ssh-auth")
expect(plan.channel_stage).to_equal("simple-ssh-channel")
expect(plan.command_stage).to_equal("simple-host-process-exec")
```

</details>

#### builds async SimpleOS SSH release plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = pure_server_simpleos_ssh_release_plan()
expect(plan.release_ready).to_be(true)
expect(plan.uses_simple_protocol).to_be(true)
expect(plan.adapter_name).to_equal("simpleos-kernel-host-access")
expect(plan.version_exchange_stage).to_equal("simple-ssh-version-exchange")
expect(plan.command_stage).to_equal("simple-host-process-exec")
```

</details>

#### blocks async SSH release plans for native bypass adapters

- caps: pure server hosted linux caps
   - Expected: plan.version_exchange_stage equals `blocked`
   - Expected: plan.kex_stage equals `blocked`
   - Expected: plan.auth_stage equals `blocked`
   - Expected: plan.channel_stage equals `blocked`
   - Expected: plan.command_stage equals `blocked`
   - Expected: plan.reason equals `ssh release adapter cannot use native protocol bypass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = PureServerHostAccessAdapter(
    name: "rt-ssh-server-wrapper",
    target: PureServerHostTarget.HostedLinux,
    caps: pure_server_hosted_linux_caps(),
    uses_native_protocol_bypass: true,
    description: "bad"
)
val plan = pure_server_ssh_release_plan(adapter)
expect(plan.release_ready).to_be(false)
expect(plan.uses_simple_protocol).to_be(false)
expect(plan.version_exchange_stage).to_equal("blocked")
expect(plan.kex_stage).to_equal("blocked")
expect(plan.auth_stage).to_equal("blocked")
expect(plan.channel_stage).to_equal("blocked")
expect(plan.command_stage).to_equal("blocked")
expect(plan.reason).to_equal("ssh release adapter cannot use native protocol bypass")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/net/pure_server_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- async pure server release routing policy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
