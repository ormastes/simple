# Visibility Metadata Specification

> Tests covering LSP Visibility Metadata.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Visibility Metadata Specification

## Scenarios

### LSP Visibility Metadata

#### formats public symbols with exported provenance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- formats public symbols with exported provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats public symbols with exported provenance")
val symbol = VisibilitySymbol(name: "Router", visibility: VisibilitySurface.Public)
val detail = format_visibility_detail(symbol, "crate.sys.http", true)

check(detail.contains("public"))
check(detail.contains("exported from crate.sys.http"))
```

</details>

#### formats boundary symbols with boundary provenance

- formats boundary symbols with boundary provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats boundary symbols with boundary provenance")
val symbol = VisibilitySymbol(name: "route_debug", visibility: VisibilitySurface.Boundary)
val detail = format_visibility_detail(symbol, "crate.sys.http", false)

check(detail == "boundary (boundary: crate.sys.http)")
```

</details>

#### keeps private symbols private in metadata

- keeps private symbols private in metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps private symbols private in metadata")
val symbol = VisibilitySymbol(name: "internal_helper", visibility: VisibilitySurface.Private)
val detail = format_visibility_detail(symbol, "crate.sys.http", false)

check(detail == "private")
```

</details>

#### filters private symbols from completion and workspace symbol surfaces

- filters private symbols from completion and workspace symbol surfaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters private symbols from completion and workspace symbol surfaces")
check(should_include_in_completion(VisibilitySurface.Public))
check(should_include_in_completion(VisibilitySurface.Boundary))
check(not should_include_in_completion(VisibilitySurface.Private))
check(should_include_in_workspace(VisibilitySurface.Public))
check(should_include_in_workspace(VisibilitySurface.Boundary))
check(not should_include_in_workspace(VisibilitySurface.Private))
```

</details>

#### ranks public before boundary before private

- ranks public before boundary before private


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ranks public before boundary before private")
check(visibility_rank(VisibilitySurface.Public) < visibility_rank(VisibilitySurface.Boundary))
check(visibility_rank(VisibilitySurface.Boundary) < visibility_rank(VisibilitySurface.Private))
```

</details>

#### ranks exact workspace matches before prefix and substring matches

- ranks exact workspace matches before prefix and substring matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ranks exact workspace matches before prefix and substring matches")
val exact = workspace_match_rank("query", "query", VisibilitySurface.Public)
val prefix = workspace_match_rank("query_visibility", "query", VisibilitySurface.Public)
val substring = workspace_match_rank("visibility_query", "query", VisibilitySurface.Public)

check(exact < prefix)
check(prefix < substring)
```

</details>

#### prefers more visible workspace results when match quality ties

- prefers more visible workspace results when match quality ties


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefers more visible workspace results when match quality ties")
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
| Source | `test/unit/app/lsp/visibility_metadata_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LSP Visibility Metadata.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d170baf9531bdf8a154b2960f3a892f952352a89666dc0357a47525238e44fb8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d170baf9531bdf8a154b2960f3a892f952352a89666dc0357a47525238e44fb8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d170baf9531bdf8a154b2960f3a892f952352a89666dc0357a47525238e44fb8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/lsp/visibility_metadata_spec.spl
mirror: doc/06_spec/unit/app/lsp/visibility_metadata_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/lsp/visibility_metadata_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/lsp/visibility_metadata_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/lsp/visibility_metadata_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats public symbols with exported provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/visibility_metadata_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats boundary symbols with boundary provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/visibility_metadata_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps private symbols private in metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
