# Worker Static File Specification

> <details>

<!-- sdn-diagram:id=worker_static_file_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=worker_static_file_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

worker_static_file_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=worker_static_file_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Worker Static File Specification

## Scenarios

### HTTP worker static-file routing

#### uses portable body sends for normal responses

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = portable_net_backend_capabilities()
val resp = build_ok("hello", "text/plain")

expect(worker_static_file_route(caps, resp)).to_equal("body")
```

</details>

#### falls back to portable reads when sendfile is unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = portable_net_backend_capabilities()
val resp = build_file_response("/tmp/large.bin", "application/octet-stream", 131072)

expect(worker_static_file_route(caps, resp)).to_equal("portable-read")
```

</details>

#### uses sendfile only when the backend reports support

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = net_backend_capabilities("sendfile-test", true, true, true, false)
val resp = build_file_response("/tmp/large.bin", "application/octet-stream", 131072)

expect(worker_static_file_route(caps, resp)).to_equal("sendfile")
```

</details>

#### does not route to sendfile for a zero-copy-only backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = net_backend_capabilities("zero-copy-only", true, true, false, true)
val resp = build_file_response("/tmp/large.bin", "application/octet-stream", 131072)

expect(worker_static_file_route(caps, resp)).to_equal("portable-read")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/http_server/worker_static_file_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HTTP worker static-file routing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
