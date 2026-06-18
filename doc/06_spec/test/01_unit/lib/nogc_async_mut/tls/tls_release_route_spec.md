# Tls Release Route Specification

> <details>

<!-- sdn-diagram:id=tls_release_route_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tls_release_route_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tls_release_route_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tls_release_route_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tls Release Route Specification

## Scenarios

### TLS release-mode route

#### builds release-mode route through Simple HTTPS protocol for hosted Linux

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = AsyncTlsListener.release_route_for_target(PureServerHostTarget.HostedLinux)
expect(route.is_ok()).to_be(true)
val decision = route.unwrap()
expect(decision.uses_simple_protocol).to_be(true)
expect(decision.allows_native_protocol_bypass).to_be(false)
```

</details>

#### builds release-mode route through Simple HTTPS protocol for SimpleOS

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = AsyncTlsListener.release_route_for_target(PureServerHostTarget.SimpleOS)
expect(route.is_ok()).to_be(true)
val decision = route.unwrap()
expect(decision.uses_simple_protocol).to_be(true)
expect(decision.allows_native_protocol_bypass).to_be(false)
```

</details>

#### builds release-mode HTTPS plan through Simple TLS and HTTP stages for hosted Linux

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = AsyncTlsListener.release_plan_for_target(PureServerHostTarget.HostedLinux)
expect(plan.release_ready).to_be(true)
expect(plan.uses_simple_protocol).to_be(true)
expect(plan.adapter_name).to_equal("hosted-linux-rt-host-access")
expect(plan.tls_stage).to_equal("simple-tls12-server")
expect(plan.http_stage).to_equal("simple-http-response")
```

</details>

#### builds release-mode HTTPS plan through the same stages for SimpleOS

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = AsyncTlsListener.release_plan_for_target(PureServerHostTarget.SimpleOS)
expect(plan.release_ready).to_be(true)
expect(plan.uses_simple_protocol).to_be(true)
expect(plan.adapter_name).to_equal("simpleos-kernel-host-access")
expect(plan.tls_stage).to_equal("simple-tls12-server")
expect(plan.http_stage).to_equal("simple-http-response")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/tls/tls_release_route_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TLS release-mode route

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
