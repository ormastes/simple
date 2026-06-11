# Sendfile Routing Specification

> Validates the sendfile routing module:

<!-- sdn-diagram:id=sendfile_routing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sendfile_routing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sendfile_routing_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sendfile_routing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sendfile Routing Specification

Validates the sendfile routing module:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | FR-NET-0003 (WQ-2) |
| Category | Stdlib / HTTP / Static-File Routing |
| Difficulty | 2/5 |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/http/sendfile_routing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the sendfile routing module:
- portable-read fallback when sendfile unavailable
- sendfile selected when supported
- zero-copy does NOT route to sendfile when unsupported
- explicit backend label returned for the verification gate

## Scenarios

### Portable-read fallback when sendfile unavailable (WQ-2a)

#### portable backend with file body routes to PortableRead

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = sendfile_caps_portable("poll-socket")
val backend = route_sendfile(caps, true)
val label = sendfile_backend_label(backend)
expect(label).to_equal("portable-read")
```

</details>

#### portable backend detection returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = sendfile_caps_portable("poll-socket")
expect(detect_sendfile_support(caps)).to_equal(false)
```

</details>

#### portable backend guard passes for PortableRead

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = sendfile_caps_portable("poll-socket")
val backend = route_sendfile(caps, true)
expect(sendfile_guard_ok(caps, backend)).to_equal(true)
```

</details>

### Sendfile selected when supported (WQ-2b)

#### sendfile backend with file body routes to Sendfile

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = sendfile_caps_with_sendfile("io-uring")
val backend = route_sendfile(caps, true)
val label = sendfile_backend_label(backend)
expect(label).to_equal("sendfile")
```

</details>

#### sendfile backend detection returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = sendfile_caps_with_sendfile("io-uring")
expect(detect_sendfile_support(caps)).to_equal(true)
```

</details>

#### full backend with file body routes to Sendfile

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = sendfile_caps_full("io-uring-zc")
val backend = route_sendfile(caps, true)
val label = sendfile_backend_label(backend)
expect(label).to_equal("sendfile")
```

</details>

#### sendfile guard passes for Sendfile on capable backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = sendfile_caps_with_sendfile("io-uring")
val backend = route_sendfile(caps, true)
expect(sendfile_guard_ok(caps, backend)).to_equal(true)
```

</details>

### Zero-copy does NOT route to sendfile when unsupported (WQ-2c)

#### zero-copy-only backend with file body routes to PortableRead

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = sendfile_caps_with_zero_copy("dpdk-zc")
val backend = route_sendfile(caps, true)
val label = sendfile_backend_label(backend)
expect(label).to_equal("portable-read")
```

</details>

#### zero-copy-only backend detection returns false for sendfile

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = sendfile_caps_with_zero_copy("dpdk-zc")
expect(detect_sendfile_support(caps)).to_equal(false)
```

</details>

#### zero-copy-only guard rejects manually constructed Sendfile

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = sendfile_caps_with_zero_copy("dpdk-zc")
expect(sendfile_guard_ok(caps, SendfileBackend.Sendfile)).to_equal(false)
```

</details>

#### zero-copy-only guard passes for PortableRead

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = sendfile_caps_with_zero_copy("dpdk-zc")
expect(sendfile_guard_ok(caps, SendfileBackend.PortableRead)).to_equal(true)
```

</details>

### Explicit backend label for verification gate (WQ-2d)

#### Sendfile label is sendfile

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sendfile_backend_label(SendfileBackend.Sendfile)).to_equal("sendfile")
```

</details>

#### PortableRead label is portable-read

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sendfile_backend_label(SendfileBackend.PortableRead)).to_equal("portable-read")
```

</details>

#### Unsupported label is unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sendfile_backend_label(SendfileBackend.Unsupported)).to_equal("unsupported")
```

</details>

#### no-file-body routes to Unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = sendfile_caps_with_sendfile("io-uring")
val backend = route_sendfile(caps, false)
val label = sendfile_backend_label(backend)
expect(label).to_equal("unsupported")
```

</details>

#### guard passes for Unsupported on any backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = sendfile_caps_portable("poll-socket")
expect(sendfile_guard_ok(caps, SendfileBackend.Unsupported)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
