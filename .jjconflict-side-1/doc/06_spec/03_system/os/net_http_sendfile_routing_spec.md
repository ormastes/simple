# Net Http Sendfile Routing Specification

> <details>

<!-- sdn-diagram:id=net_http_sendfile_routing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=net_http_sendfile_routing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

net_http_sendfile_routing_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=net_http_sendfile_routing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Net Http Sendfile Routing Specification

## Scenarios

### FR-NET-0003 HTTP static-file capability routing

#### worker startup capability model

#### summarizes portable backend capabilities for worker records

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = portable_net_backend_capabilities()
expect(net_backend_summary(caps)).to_equal("portable-socket:portable")
expect(net_backend_can_accelerate_static_files(caps)).to_equal(false)
```

</details>

#### summarizes sendfile-capable backends as static-file accelerators

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = net_backend_capabilities("sendfile-test", true, true, true, false)
expect(net_backend_summary(caps)).to_equal("sendfile-test:sendfile")
expect(net_backend_can_accelerate_static_files(caps)).to_equal(true)
```

</details>

#### static file route selection

#### keeps ordinary response bodies on the portable body path

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = net_backend_capabilities("sendfile-test", true, true, true, false)
expect(net_backend_static_file_route(caps, false)).to_equal("body")
```

</details>

#### uses portable read plus send when sendfile is unavailable

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = portable_net_backend_capabilities()
expect(net_backend_static_file_route(caps, true)).to_equal("portable-read")
```

</details>

#### uses sendfile only when the backend explicitly supports sendfile

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = net_backend_capabilities("sendfile-test", true, true, true, false)
expect(net_backend_static_file_route(caps, true)).to_equal("sendfile")
```

</details>

#### does not treat zero-copy-only as a file-to-socket sendfile path

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = net_backend_capabilities("zero-copy-only", true, true, false, true)
expect(net_backend_can_accelerate_static_files(caps)).to_equal(true)
expect(net_backend_static_file_route(caps, true)).to_equal("portable-read")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/net_http_sendfile_routing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FR-NET-0003 HTTP static-file capability routing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
