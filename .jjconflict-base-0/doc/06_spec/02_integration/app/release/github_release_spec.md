# Github Release Specification

> 1. expect basename

<!-- sdn-diagram:id=github_release_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=github_release_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

github_release_spec -> std
github_release_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=github_release_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Github Release Specification

## Scenarios

### GitHub release helpers

#### basename

#### returns the final path segment

1. expect basename


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect basename("release/simple-bootstrap-1.0.0.spk") to_equal "simple-bootstrap-1.0.0.spk"
```

</details>

#### returns the original text when no slash exists

1. expect basename


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect basename("artifact.txt") to_equal "artifact.txt"
```

</details>

#### strip_upload_url_template

#### removes github upload url templates

1. expect strip upload url template


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "https://uploads.github.com/repos/org/repo/releases/1/assets{?name,label}"
expect strip_upload_url_template(raw) to_equal "https://uploads.github.com/repos/org/repo/releases/1/assets"
```

</details>

#### keeps plain urls unchanged

1. expect strip upload url template


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "https://uploads.github.com/repos/org/repo/releases/1/assets"
expect strip_upload_url_template(raw) to_equal raw
```

</details>

#### guess_content_type

#### detects text checksum files

1. expect guess content type


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect guess_content_type("SHA256SUMS.txt") to_equal "text/plain; charset=utf-8"
```

</details>

#### detects gzip-like bootstrap packages

1. expect guess content type


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect guess_content_type("simple-bootstrap-1.0.0.spk") to_equal "application/gzip"
```

</details>

#### falls back to octet stream

1. expect guess content type


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect guess_content_type("simple-binary") to_equal "application/octet-stream"
```

</details>

#### build_release_payload

#### includes required github release fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = build_release_payload("v1.2.3", "Simple Language v1.2.3", "notes", "", false, false)
expect payload to_contain "\"tag_name\": \"v1.2.3\""
expect payload to_contain "\"name\": \"Simple Language v1.2.3\""
expect payload to_contain "\"draft\": false"
```

</details>

#### adds target_commitish when provided

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = build_release_payload("v1.2.3", "Simple", "notes", "abc123", false, true)
expect payload to_contain "\"target_commitish\": \"abc123\""
expect payload to_contain "\"prerelease\": true"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/release/github_release_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GitHub release helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
