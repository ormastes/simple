# Visibility Metadata Specification

> 1. check

<!-- sdn-diagram:id=visibility_metadata_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=visibility_metadata_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

visibility_metadata_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=visibility_metadata_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Visibility Metadata Specification

## Scenarios

### LSP Visibility Metadata

#### formats public symbols with exported provenance

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbol = VisibilitySymbol(name: "Router", visibility: VisibilitySurface.Public)
val detail = format_visibility_detail(symbol, "crate.sys.http", true)

check(detail.contains("public"))
check(detail.contains("exported from crate.sys.http"))
```

</details>

#### formats boundary symbols with boundary provenance

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbol = VisibilitySymbol(name: "route_debug", visibility: VisibilitySurface.Boundary)
val detail = format_visibility_detail(symbol, "crate.sys.http", false)

check(detail == "boundary (boundary: crate.sys.http)")
```

</details>

#### keeps private symbols private in metadata

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbol = VisibilitySymbol(name: "internal_helper", visibility: VisibilitySurface.Private)
val detail = format_visibility_detail(symbol, "crate.sys.http", false)

check(detail == "private")
```

</details>

#### filters private symbols from completion and workspace symbol surfaces

1. check
2. check
3. check
4. check
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(should_include_in_completion(VisibilitySurface.Public))
check(should_include_in_completion(VisibilitySurface.Boundary))
check(not should_include_in_completion(VisibilitySurface.Private))
check(should_include_in_workspace(VisibilitySurface.Public))
check(should_include_in_workspace(VisibilitySurface.Boundary))
check(not should_include_in_workspace(VisibilitySurface.Private))
```

</details>

#### ranks public before boundary before private

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(visibility_rank(VisibilitySurface.Public) < visibility_rank(VisibilitySurface.Boundary))
check(visibility_rank(VisibilitySurface.Boundary) < visibility_rank(VisibilitySurface.Private))
```

</details>

#### ranks exact workspace matches before prefix and substring matches

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exact = workspace_match_rank("query", "query", VisibilitySurface.Public)
val prefix = workspace_match_rank("query_visibility", "query", VisibilitySurface.Public)
val substring = workspace_match_rank("visibility_query", "query", VisibilitySurface.Public)

check(exact < prefix)
check(prefix < substring)
```

</details>

#### prefers more visible workspace results when match quality ties

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val public_rank = workspace_match_rank("query_visibility", "query", VisibilitySurface.Public)
val boundary_rank = workspace_match_rank("query_visibility", "query", VisibilitySurface.Boundary)
val private_rank = workspace_match_rank("query_visibility", "query", VisibilitySurface.Private)

check(public_rank < boundary_rank)
check(boundary_rank < private_rank)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp/visibility_metadata_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LSP Visibility Metadata

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
