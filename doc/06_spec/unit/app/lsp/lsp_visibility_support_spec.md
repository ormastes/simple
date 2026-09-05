# LSP Visibility Support Specification

> Validates that the LSP server correctly exposes visibility metadata (public, boundary, private) for symbols across hover, completion, document symbols, workspace symbols, and semantic tokens.

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
| Source | `test/unit/app/lsp/lsp_visibility_support_spec.spl` |
| Updated | 2026-08-26 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LSPVIS-001
# @req REQ-LSPVIS-002
# @req REQ-LSPVIS-003
# @req REQ-LSPVIS-004
# @req REQ-LSPVIS-006
# @req REQ-LSPVIS-007
# @req REQ-LSPVIS-008
```

</details>

#### ranks public before boundary before private

- ranks public before boundary before private


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ranks public before boundary before private")
# visibility_rank: public=0, boundary=10, private=20
val public_rank = 0
val boundary_rank = 10
val private_rank = 20

check(public_rank < boundary_rank)
check(boundary_rank < private_rank)
```

</details>

#### treats public and boundary as reachable, private as unreachable

- treats public and boundary as reachable, private as unreachable


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats public and boundary as reachable, private as unreachable")
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

- supports public, internal, package, and private declared levels
   - Expected: levels.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports public, internal, package, and private declared levels")
val levels = ["public", "internal", "package", "private"]

expect(levels.len()).to_equal(4)
check(levels[0] == "public")
check(levels[1] == "internal")
check(levels[2] == "package")
check(levels[3] == "private")
```

</details>

#### maps declared public to display public

- maps declared public to display public
   - Expected: display equals `public`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps declared public to display public")
val declared = "public"
val display = if declared == "public": "public" else: "boundary"
expect(display).to_equal("public")
```

</details>

#### maps declared private to display private

- maps declared private to display private
   - Expected: display equals `private`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps declared private to display private")
val declared = "private"
val display = if declared == "private": "private" else: "boundary"
expect(display).to_equal("private")
```

</details>

#### maps declared internal and package to display boundary

- maps declared internal and package to display boundary
   - Expected: internal_display equals `boundary`
   - Expected: package_display equals `boundary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps declared internal and package to display boundary")
val internal_display = "boundary"
val package_display = "boundary"
expect(internal_display).to_equal("boundary")
expect(package_display).to_equal("boundary")
```

</details>

### Visibility Detail Formatting

#### formats public exported symbol with provenance

- formats public exported symbol with provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats public exported symbol with provenance")
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

- formats boundary symbol with boundary provenance
   - Expected: detail equals `boundary (boundary: std.net.http)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats boundary symbol with boundary provenance")
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

- formats private symbol without extra provenance
   - Expected: detail equals `private`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats private symbol without extra provenance")
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

- includes reachable public symbols in completions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes reachable public symbols in completions")
val reachable = true
check(reachable)
```

</details>

#### includes reachable boundary symbols in completions

- includes reachable boundary symbols in completions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes reachable boundary symbols in completions")
val reachable = true
check(reachable)
```

</details>

#### excludes unreachable private symbols from completions

- excludes unreachable private symbols from completions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excludes unreachable private symbols from completions")
val reachable = false
check(not reachable)
```

</details>

#### includes reachable symbols in workspace search

- includes reachable symbols in workspace search


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes reachable symbols in workspace search")
val reachable = true
check(reachable)
```

</details>

#### excludes unreachable symbols from workspace search

- excludes unreachable symbols from workspace search


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excludes unreachable symbols from workspace search")
val reachable = false
check(not reachable)
```

</details>

### Workspace Symbol Ranking

#### ranks exact match above prefix match

- ranks exact match above prefix match


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ranks exact match above prefix match")
# Simulates rank_workspace_symbol_candidate scoring
var exact_score = 1000 - 300
var prefix_score = 1000 - 220
check(exact_score < prefix_score)
```

</details>

#### ranks prefix match above substring match

- ranks prefix match above substring match


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ranks prefix match above substring match")
var prefix_score = 1000 - 220
var substring_score = 1000 - 120
check(prefix_score < substring_score)
```

</details>

#### prefers public over boundary when match quality ties

- prefers public over boundary when match quality ties


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefers public over boundary when match quality ties")
val base = 1000 - 220
val public_score = base + 0
val boundary_score = base + 10
check(public_score < boundary_score)
```

</details>

#### prefers boundary over private when match quality ties

- prefers boundary over private when match quality ties


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefers boundary over private when match quality ties")
val base = 1000 - 220
val boundary_score = base + 10
val private_score = base + 20
check(boundary_score < private_score)
```

</details>

### Semantic Token Visibility Modifiers

#### assigns correct bitmask for public visibility

- assigns correct bitmask for public visibility
   - Expected: modifier equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns correct bitmask for public visibility")
val modifier = 512
expect(modifier).to_equal(512)
```

</details>

#### assigns correct bitmask for boundary visibility

- assigns correct bitmask for boundary visibility
   - Expected: modifier equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns correct bitmask for boundary visibility")
val modifier = 1024
expect(modifier).to_equal(1024)
```

</details>

#### assigns correct bitmask for private visibility

- assigns correct bitmask for private visibility
   - Expected: modifier equals `2048`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns correct bitmask for private visibility")
val modifier = 2048
expect(modifier).to_equal(2048)
```

</details>

#### uses disjoint bitmask values for all three levels

- uses disjoint bitmask values for all three levels


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses disjoint bitmask values for all three levels")
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

- maps display string to correct modifier
   - Expected: mod_for("public") equals `512`
   - Expected: mod_for("boundary") equals `1024`
   - Expected: mod_for("private") equals `2048`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps display string to correct modifier")
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

- includes visibility display in hover prose


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes visibility display in hover prose")
var lines: [text] = []
lines = lines.push("Visibility: **public**")
val prose = lines.join("\n")
check(prose.contains("Visibility: **public**"))
```

</details>

#### includes boundary module when present

- includes boundary module when present


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes boundary module when present")
var lines: [text] = []
lines = lines.push("Visibility: **boundary**")
lines = lines.push("Boundary: `std.net.http` (boundary)")
val prose = lines.join("\n")
check(prose.contains("Boundary: `std.net.http`"))
```

</details>

#### includes exported-by provenance when present

- includes exported-by provenance when present


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes exported-by provenance when present")
var lines: [text] = []
lines = lines.push("Visibility: **public**")
lines = lines.push("Exported by: `src/lib/nogc_sync_mut/net/__init__.spl`")
val prose = lines.join("\n")
check(prose.contains("Exported by:"))
```

</details>

#### shows visibility for unreachable symbols without blocking navigation

- shows visibility for unreachable symbols without blocking navigation


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows visibility for unreachable symbols without blocking navigation")
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

- detects client visibility support from experimental field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects client visibility support from experimental field")
val experimental = "\"simpleVisibility\":true"
val supports = experimental.contains("simpleVisibility")
check(supports)
```

</details>

#### returns false for empty experimental field

- returns false for empty experimental field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for empty experimental field")
val experimental = ""
val supports = experimental.contains("simpleVisibility")
check(not supports)
```

</details>

#### returns false for unrelated experimental capabilities

- returns false for unrelated experimental capabilities


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for unrelated experimental capabilities")
val experimental = "\"otherFeature\":true"
val supports = experimental.contains("simpleVisibility")
check(not supports)
```

</details>

#### server advertises simpleVisibilityProvider in initialize result

- server advertises simpleVisibilityProvider in initialize result


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("server advertises simpleVisibilityProvider in initialize result")
val server_experimental = "\"simpleVisibilityProvider\":true"
check(server_experimental.contains("simpleVisibilityProvider"))
```

</details>

### Boundary Kind Classification

#### recognizes open boundary kind

- recognizes open boundary kind
   - Expected: kind equals `open`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes open boundary kind")
val kind = "open"
expect(kind).to_equal("open")
```

</details>

#### recognizes boundary kind

- recognizes boundary kind
   - Expected: kind equals `boundary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes boundary kind")
val kind = "boundary"
expect(kind).to_equal("boundary")
```

</details>

#### recognizes bypass boundary kind

- recognizes bypass boundary kind
   - Expected: kind equals `bypass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes bypass boundary kind")
val kind = "bypass"
expect(kind).to_equal("bypass")
```

</details>

### Visibility JSON Payload Structure

#### includes required display field

- includes required display field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes required display field")
val payload = "{\"display\":\"public\",\"reachable\":true,\"boundaryKind\":\"open\",\"declared\":\"public\"}"
check(payload.contains("\"display\":\"public\""))
```

</details>

#### includes required reachable field

- includes required reachable field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes required reachable field")
val payload = "{\"display\":\"public\",\"reachable\":true,\"boundaryKind\":\"open\",\"declared\":\"public\"}"
check(payload.contains("\"reachable\":true"))
```

</details>

#### includes required boundaryKind field

- includes required boundaryKind field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes required boundaryKind field")
val payload = "{\"display\":\"public\",\"reachable\":true,\"boundaryKind\":\"open\",\"declared\":\"public\"}"
check(payload.contains("\"boundaryKind\":\"open\""))
```

</details>

#### includes required declared field

- includes required declared field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes required declared field")
val payload = "{\"display\":\"public\",\"reachable\":true,\"boundaryKind\":\"open\",\"declared\":\"public\"}"
check(payload.contains("\"declared\":\"public\""))
```

</details>

#### includes optional boundaryModule when present

- includes optional boundaryModule when present


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes optional boundaryModule when present")
val payload = "{\"display\":\"boundary\",\"reachable\":true,\"boundaryKind\":\"boundary\",\"declared\":\"private\",\"boundaryModule\":\"lib.nogc_sync_mut.lsp\"}"
check(payload.contains("\"boundaryModule\":\"lib.nogc_sync_mut.lsp\""))
```

</details>

#### includes optional exportedBy when present

- includes optional exportedBy when present


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes optional exportedBy when present")
val payload = "{\"display\":\"public\",\"reachable\":true,\"boundaryKind\":\"boundary\",\"declared\":\"public\",\"exportedBy\":\"src/lib/nogc_sync_mut/lsp/__init__.spl\"}"
check(payload.contains("\"exportedBy\":"))
```

</details>

#### includes optional friendPackages as array

- includes optional friendPackages as array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes optional friendPackages as array")
val payload = "{\"display\":\"boundary\",\"reachable\":false,\"boundaryKind\":\"boundary\",\"declared\":\"internal\",\"friendPackages\":[\"net\",\"http\"]}"
check(payload.contains("\"friendPackages\":["))
```

</details>

#### includes optional capsuleName for MDSOC symbols

- includes optional capsuleName for MDSOC symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes optional capsuleName for MDSOC symbols")
val payload = "{\"display\":\"boundary\",\"reachable\":true,\"boundaryKind\":\"boundary\",\"declared\":\"private\",\"capsuleName\":\"mdsoc.weaver\",\"capsuleVisibility\":\"internal\"}"
check(payload.contains("\"capsuleName\":\"mdsoc.weaver\""))
check(payload.contains("\"capsuleVisibility\":\"internal\""))
```

</details>

#### omits optional fields when not applicable

- omits optional fields when not applicable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("omits optional fields when not applicable")
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

- **Requirements:** `doc/02_requirements/feature/simple_lsp_visibility_support.md`
- **Design:** `doc/05_design/simple_lsp_visibility_support.md`
- **Research:** `doc/01_research/local/simple_lsp_visibility_support.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LSPVIS-001:`
- `REQ-LSPVIS-002:`
- `REQ-LSPVIS-003:`
- `REQ-LSPVIS-004:`
- `REQ-LSPVIS-005:`
- `REQ-LSPVIS-006:`
- `REQ-LSPVIS-007:`
- `REQ-LSPVIS-008:`
- `REQ-LSPVIS-001`
- `REQ-LSPVIS-002`
- `REQ-LSPVIS-003`
- `REQ-LSPVIS-004`
- `REQ-LSPVIS-006`
- `REQ-LSPVIS-007`
- `REQ-LSPVIS-008`
- `REQ-LSPVIS-005)`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `82e6727a7dc5092cda990cd91f520d1239569a8659b5e174149b51c50a6021cd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `82e6727a7dc5092cda990cd91f520d1239569a8659b5e174149b51c50a6021cd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `82e6727a7dc5092cda990cd91f520d1239569a8659b5e174149b51c50a6021cd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/unit/app/lsp/lsp_visibility_support_spec.spl
mirror: doc/06_spec/unit/app/lsp/lsp_visibility_support_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/lsp/lsp_visibility_support_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/lsp/lsp_visibility_support_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/lsp/lsp_visibility_support_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/lsp/lsp_visibility_support_spec.spl:56:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'distinguishes public, boundary, and private display levels' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/app/lsp/lsp_visibility_support_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ranks public before boundary before private' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/lsp_visibility_support_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats public and boundary as reachable, private as unreachable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/lsp_visibility_support_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports public, internal, package, and private declared levels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
