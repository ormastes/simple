# Simple Portal Content Db Specification

> <details>

<!-- sdn-diagram:id=simple_portal_content_db_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_portal_content_db_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_portal_content_db_spec -> std
simple_portal_content_db_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_portal_content_db_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Portal Content Db Specification

## Scenarios

### simple_portal content db

#### loads the packaged portal content root

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = portal_content_db_load(simple_portal_default_app_root())
expect(result.is_ok()).to_equal(true)
```

</details>

#### prefers a complete filesystem-backed data root over a missing app root

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data_root = simple_portal_default_app_root()
val result = portal_content_db_load_resolved("/tmp/simple_portal_missing_app_root", data_root)
expect(result.is_ok()).to_equal(true)
val source = result.unwrap()
expect(source.root).to_equal(data_root)
expect(source.db.pages[0].slug).to_equal("docs")
```

</details>

#### rejects malformed page body paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = portal_content_db_from_text(
    "docs|Docs|Summary|../escape.html",
    "hello-world|Hello|simple|client|Summary|examples/hello.simple",
    "1.0.0|stable|Stable|https://example.com",
    "repo|Repo|repo|https://example.com"
)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects unsupported example execution modes

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = portal_content_db_from_text(
    "docs|Docs|Summary|pages/docs.html",
    "hello-world|Hello|simple|shell|Summary|examples/hello.simple",
    "1.0.0|stable|Stable|https://example.com",
    "repo|Repo|repo|https://example.com"
)
expect(result.is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/simple_portal/simple_portal_content_db_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- simple_portal content db

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
