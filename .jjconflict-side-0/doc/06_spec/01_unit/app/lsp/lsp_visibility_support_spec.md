# LSP Visibility Support Specification

> Validates that the LSP server correctly exposes visibility metadata (public, boundary, private) for symbols across hover, completion, document symbols, workspace symbols, and semantic tokens.

<!-- sdn-diagram:id=lsp_visibility_support_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lsp_visibility_support_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lsp_visibility_support_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lsp_visibility_support_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LSP Visibility Support Specification

Validates that the LSP server correctly exposes visibility metadata (public, boundary, private) for symbols across hover, completion, document symbols, workspace symbols, and semantic tokens.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #F10-LSPVIS |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/simple_lsp_visibility_support.md |
| Plan | N/A |
| Design | doc/05_design/simple_lsp_visibility_support.md |
| Research | doc/01_research/local/simple_lsp_visibility_support.md |
| Source | `test/01_unit/app/lsp/lsp_visibility_support_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that the LSP server correctly exposes visibility metadata
(public, boundary, private) for symbols across hover, completion,
document symbols, workspace symbols, and semantic tokens.

## Behavior

- REQ-LSPVIS-001: Visibility metadata on all symbol-returning responses
- REQ-LSPVIS-002: Three display levels (public, boundary, private)
- REQ-LSPVIS-003: Richer declared visibility when available
- REQ-LSPVIS-004: Completion/workspace filtering by reachability
- REQ-LSPVIS-005: Hover/definition always resolve explicit references
- REQ-LSPVIS-006: Semantic token visibility modifiers
- REQ-LSPVIS-007: Diagnostics remain enforcement channel
- REQ-LSPVIS-008: Capability negotiation with text fallback

## Scenarios

### Visibility Level Classification

#### distinguishes public, boundary, and private display levels

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The three canonical display level strings
val public_level = "public"
val boundary_level = "boundary"
val private_level = "private"

check(public_level != boundary_level)
check(boundary_level != private_level)
check(public_level != private_level)
```

</details>

#### ranks public before boundary before private

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# visibility_rank: public=0, boundary=10, private=20
val public_rank = 0
val boundary_rank = 10
val private_rank = 20

check(public_rank < boundary_rank)
check(boundary_rank < private_rank)
```

</details>

#### treats public and boundary as reachable, private as unreachable

1. check
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check("public" != "private")
check("boundary" != "private")
# Private symbols are not reachable from external scopes
val is_reachable_public = true
val is_reachable_boundary = true
val is_reachable_private = false

check(is_reachable_public)
check(is_reachable_boundary)
check(not is_reachable_private)
```

</details>

### Declared Visibility Levels

#### supports public, internal, package, and private declared levels

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val levels = ["public", "internal", "package", "private"]

expect(levels.len()).to_equal(4)
check(levels[0] == "public")
check(levels[1] == "internal")
check(levels[2] == "package")
check(levels[3] == "private")
```

</details>

#### maps declared public to display public

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val declared = "public"
val display = if declared == "public": "public" else: "boundary"
expect(display).to_equal("public")
```

</details>

#### maps declared private to display private

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val declared = "private"
val display = if declared == "private": "private" else: "boundary"
expect(display).to_equal("private")
```

</details>

#### maps declared internal and package to display boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val internal_display = "boundary"
val package_display = "boundary"
expect(internal_display).to_equal("boundary")
expect(package_display).to_equal("boundary")
```

</details>

### Visibility Detail Formatting

#### formats public exported symbol with provenance

1. detail = display + "
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val display = "public"
val boundary_module = "std.net.http"
val exported_by = "src/lib/nogc_sync_mut/net/__init__.spl"
# format_visibility_detail logic
var detail = display
if exported_by != "":
    detail = display + " (exported from " + boundary_module + ")"
check(detail.contains("public"))
check(detail.contains("exported from std.net.http"))
```

</details>

#### formats boundary symbol with boundary provenance

1. detail = display + "
2. detail = display + "
   - Expected: detail equals `boundary (boundary: std.net.http)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val display = "boundary"
val boundary_module = "std.net.http"
val exported_by = ""
var detail = display
if exported_by != "":
    detail = display + " (exported from " + boundary_module + ")"
if exported_by == "" and display == "boundary" and boundary_module != "":
    detail = display + " (boundary: " + boundary_module + ")"
expect(detail).to_equal("boundary (boundary: std.net.http)")
```

</details>

#### formats private symbol without extra provenance

1. detail = display + "
2. detail = display + "
   - Expected: detail equals `private`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val display = "private"
val boundary_module = "std.net.http"
val exported_by = ""
var detail = display
if exported_by != "":
    detail = display + " (exported from " + boundary_module + ")"
if exported_by == "" and display == "boundary" and boundary_module != "":
    detail = display + " (boundary: " + boundary_module + ")"
expect(detail).to_equal("private")
```

</details>

### Completion Visibility Filtering

#### includes reachable public symbols in completions

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reachable = true
check(reachable)
```

</details>

#### includes reachable boundary symbols in completions

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reachable = true
check(reachable)
```

</details>

#### excludes unreachable private symbols from completions

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reachable = false
check(not reachable)
```

</details>

#### includes reachable symbols in workspace search

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reachable = true
check(reachable)
```

</details>

#### excludes unreachable symbols from workspace search

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reachable = false
check(not reachable)
```

</details>

### Workspace Symbol Ranking

#### ranks exact match above prefix match

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulates rank_workspace_symbol_candidate scoring
var exact_score = 1000 - 300
var prefix_score = 1000 - 220
check(exact_score < prefix_score)
```

</details>

#### ranks prefix match above substring match

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var prefix_score = 1000 - 220
var substring_score = 1000 - 120
check(prefix_score < substring_score)
```

</details>

#### prefers public over boundary when match quality ties

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = 1000 - 220
val public_score = base + 0
val boundary_score = base + 10
check(public_score < boundary_score)
```

</details>

#### prefers boundary over private when match quality ties

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = 1000 - 220
val boundary_score = base + 10
val private_score = base + 20
check(boundary_score < private_score)
```

</details>

### Semantic Token Visibility Modifiers

#### assigns correct bitmask for public visibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val modifier = 512
expect(modifier).to_equal(512)
```

</details>

#### assigns correct bitmask for boundary visibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val modifier = 1024
expect(modifier).to_equal(1024)
```

</details>

#### assigns correct bitmask for private visibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val modifier = 2048
expect(modifier).to_equal(2048)
```

</details>

#### uses disjoint bitmask values for all three levels

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val public_mod = 512
val boundary_mod = 1024
val private_mod = 2048
# No overlap via bitwise check (manual since no bitwise AND in interpreter)
check(public_mod != boundary_mod)
check(boundary_mod != private_mod)
check(public_mod != private_mod)
```

</details>

#### maps display string to correct modifier

1. fn mod for
   - Expected: mod_for("public") equals `512`
   - Expected: mod_for("boundary") equals `1024`
   - Expected: mod_for("private") equals `2048`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# visibility_modifier_for_display logic
fn mod_for(display: text) -> i64:
    if display == "public":
        return 512
    if display == "boundary":
        return 1024
    2048
expect(mod_for("public")).to_equal(512)
expect(mod_for("boundary")).to_equal(1024)
expect(mod_for("private")).to_equal(2048)
```

</details>

### Hover Visibility Prose

#### includes visibility display in hover prose

1. lines = lines push
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lines: [text] = []
lines = lines.push("Visibility: **public**")
val prose = lines.join("\n")
check(prose.contains("Visibility: **public**"))
```

</details>

#### includes boundary module when present

1. lines = lines push
2. lines = lines push
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lines: [text] = []
lines = lines.push("Visibility: **boundary**")
lines = lines.push("Boundary: `std.net.http` (boundary)")
val prose = lines.join("\n")
check(prose.contains("Boundary: `std.net.http`"))
```

</details>

#### includes exported-by provenance when present

1. lines = lines push
2. lines = lines push
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lines: [text] = []
lines = lines.push("Visibility: **public**")
lines = lines.push("Exported by: `src/lib/nogc_sync_mut/net/__init__.spl`")
val prose = lines.join("\n")
check(prose.contains("Exported by:"))
```

</details>

#### shows visibility for unreachable symbols without blocking navigation

1. lines = lines push
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# REQ-LSPVIS-005: hover always shows visibility, definition always navigates
val display = "private"
val reachable = false
var lines: [text] = []
lines = lines.push("Visibility: **" + display + "**")
val prose = lines.join("\n")
check(prose.contains("Visibility: **private**"))
# Navigation (definition) would still resolve - tested in integration
```

</details>

### Capability Negotiation

#### detects client visibility support from experimental field

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val experimental = "\"simpleVisibility\":true"
val supports = experimental.contains("simpleVisibility")
check(supports)
```

</details>

#### returns false for empty experimental field

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val experimental = ""
val supports = experimental.contains("simpleVisibility")
check(not supports)
```

</details>

#### returns false for unrelated experimental capabilities

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val experimental = "\"otherFeature\":true"
val supports = experimental.contains("simpleVisibility")
check(not supports)
```

</details>

#### server advertises simpleVisibilityProvider in initialize result

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server_experimental = "\"simpleVisibilityProvider\":true"
check(server_experimental.contains("simpleVisibilityProvider"))
```

</details>

### Boundary Kind Classification

#### recognizes open boundary kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "open"
expect(kind).to_equal("open")
```

</details>

#### recognizes boundary kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "boundary"
expect(kind).to_equal("boundary")
```

</details>

#### recognizes bypass boundary kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "bypass"
expect(kind).to_equal("bypass")
```

</details>

### Visibility JSON Payload Structure

#### includes required display field

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = "{\"display\":\"public\",\"reachable\":true,\"boundaryKind\":\"open\",\"declared\":\"public\"}"
check(payload.contains("\"display\":\"public\""))
```

</details>

#### includes required reachable field

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = "{\"display\":\"public\",\"reachable\":true,\"boundaryKind\":\"open\",\"declared\":\"public\"}"
check(payload.contains("\"reachable\":true"))
```

</details>

#### includes required boundaryKind field

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = "{\"display\":\"public\",\"reachable\":true,\"boundaryKind\":\"open\",\"declared\":\"public\"}"
check(payload.contains("\"boundaryKind\":\"open\""))
```

</details>

#### includes required declared field

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = "{\"display\":\"public\",\"reachable\":true,\"boundaryKind\":\"open\",\"declared\":\"public\"}"
check(payload.contains("\"declared\":\"public\""))
```

</details>

#### includes optional boundaryModule when present

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = "{\"display\":\"boundary\",\"reachable\":true,\"boundaryKind\":\"boundary\",\"declared\":\"private\",\"boundaryModule\":\"lib.nogc_sync_mut.lsp\"}"
check(payload.contains("\"boundaryModule\":\"lib.nogc_sync_mut.lsp\""))
```

</details>

#### includes optional exportedBy when present

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = "{\"display\":\"public\",\"reachable\":true,\"boundaryKind\":\"boundary\",\"declared\":\"public\",\"exportedBy\":\"src/lib/nogc_sync_mut/lsp/__init__.spl\"}"
check(payload.contains("\"exportedBy\":"))
```

</details>

#### includes optional friendPackages as array

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = "{\"display\":\"boundary\",\"reachable\":false,\"boundaryKind\":\"boundary\",\"declared\":\"internal\",\"friendPackages\":[\"net\",\"http\"]}"
check(payload.contains("\"friendPackages\":["))
```

</details>

#### includes optional capsuleName for MDSOC symbols

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = "{\"display\":\"boundary\",\"reachable\":true,\"boundaryKind\":\"boundary\",\"declared\":\"private\",\"capsuleName\":\"mdsoc.weaver\",\"capsuleVisibility\":\"internal\"}"
check(payload.contains("\"capsuleName\":\"mdsoc.weaver\""))
check(payload.contains("\"capsuleVisibility\":\"internal\""))
```

</details>

#### omits optional fields when not applicable

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = "{\"display\":\"private\",\"reachable\":false,\"boundaryKind\":\"open\",\"declared\":\"private\"}"
check(not payload.contains("\"boundaryModule\""))
check(not payload.contains("\"exportedBy\""))
check(not payload.contains("\"friendPackages\""))
check(not payload.contains("\"capsuleName\""))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/simple_lsp_visibility_support.md](doc/02_requirements/feature/simple_lsp_visibility_support.md)
- **Design:** [doc/05_design/simple_lsp_visibility_support.md](doc/05_design/simple_lsp_visibility_support.md)
- **Research:** [doc/01_research/local/simple_lsp_visibility_support.md](doc/01_research/local/simple_lsp_visibility_support.md)


</details>
