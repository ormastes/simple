# Pkg Repo Specification

> <details>

<!-- sdn-diagram:id=pkg_repo_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pkg_repo_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pkg_repo_spec -> std
pkg_repo_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pkg_repo_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pkg Repo Specification

## Scenarios

### parse_http_url

#### parses a basic URL with no port and no path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_http_url("http://repo.example.com")
expect(result.0).to_equal("repo.example.com")
expect(result.1).to_equal(80)
expect(result.2).to_equal("/")
```

</details>

#### parses a URL with explicit port and path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_http_url("http://repo.example.com:8080/index.sdn")
expect(result.0).to_equal("repo.example.com")
expect(result.1).to_equal(8080)
expect(result.2).to_equal("/index.sdn")
```

</details>

#### parses a URL with default port and sub-path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_http_url("http://pkg.simpleos.org/v1/index.sdn")
expect(result.0).to_equal("pkg.simpleos.org")
expect(result.1).to_equal(80)
expect(result.2).to_equal("/v1/index.sdn")
```

</details>

#### parses an https URL stripping scheme

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_http_url("https://secure.example.com:443/pkgs/index.sdn")
expect(result.0).to_equal("secure.example.com")
expect(result.1).to_equal(443)
expect(result.2).to_equal("/pkgs/index.sdn")
```

</details>

#### defaults to port 443 for https URL without explicit port

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_http_url("https://secure.example.com/pkgs/index.sdn")
expect(result.0).to_equal("secure.example.com")
expect(result.1).to_equal(443)
expect(result.2).to_equal("/pkgs/index.sdn")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tools/pkg/pkg_repo_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- parse_http_url

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
