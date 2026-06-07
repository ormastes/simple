# URL Types Specification

> Verifies URL and Origin entity types: construction, field access, scheme/host/port/path extraction, and origin computation. No network calls — pure value-type logic.

<!-- sdn-diagram:id=url_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=url_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

url_types_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=url_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# URL Types Specification

Verifies URL and Origin entity types: construction, field access, scheme/host/port/path extraction, and origin computation. No network calls — pure value-type logic.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #M16-AC1 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/browser_engine/net/url_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies URL and Origin entity types: construction, field access, scheme/host/port/path
extraction, and origin computation. No network calls — pure value-type logic.

## Scenarios

### Url entity type

#### when constructing a simple http URL

#### AC-1: stores scheme correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = make_http_url()
expect(u.scheme).to_equal("http")
```

</details>

#### AC-1: stores host correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = make_http_url()
expect(u.host).to_equal("example.com")
```

</details>

#### AC-1: stores default port 80 for http

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = make_http_url()
expect(u.port).to_equal(80)
```

</details>

#### AC-1: stores path correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = make_http_url()
expect(u.path).to_equal("/index.html")
```

</details>

#### when constructing an https URL with explicit port

#### AC-1: stores https scheme

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = make_https_explicit_port_url()
expect(u.scheme).to_equal("https")
```

</details>

#### AC-1: stores explicit port 8443

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = make_https_explicit_port_url()
expect(u.port).to_equal(8443)
```

</details>

#### AC-1: stores host without port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = make_https_explicit_port_url()
expect(u.host).to_equal("api.example.com")
```

</details>

#### when URL has query string

#### AC-1: stores query string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = make_url_with_query()
expect(u.query).to_equal("foo=bar&baz=1")
```

</details>

#### when URL has fragment

#### AC-1: stores fragment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = make_url_with_fragment()
expect(u.fragment).to_equal("section-2")
```

</details>

#### when URL has empty path

#### AC-1: path is empty string or slash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = make_root_url()
val ok = (u.path == "/" or u.path == "")
expect(ok).to_equal(true)
```

</details>

### Origin from Url

#### AC-5: same scheme+host+port is same origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = make_origin("https", "example.com", 443)
val b = make_origin("https", "example.com", 443)
expect(a.scheme).to_equal(b.scheme)
expect(a.host).to_equal(b.host)
expect(a.port).to_equal(b.port)
```

</details>

#### AC-5: different scheme is different origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = make_origin("http", "example.com", 80)
val b = make_origin("https", "example.com", 443)
val same = (a.scheme == b.scheme)
expect(same).to_equal(false)
```

</details>

#### AC-5: different host is different origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = make_origin("https", "example.com", 443)
val b = make_origin("https", "other.com", 443)
val same = (a.host == b.host)
expect(same).to_equal(false)
```

</details>

#### AC-5: different port is different origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = make_origin("https", "example.com", 443)
val b = make_origin("https", "example.com", 8443)
val same = (a.port == b.port)
expect(same).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
