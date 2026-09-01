# Api Tool Specification

> Tests covering Symbol Extraction Heuristic, Visibility Filtering, API Tool Helpers, Type Domain Path Normalization.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Api Tool Specification

## Scenarios

### Symbol Extraction Heuristic

#### extracts public function

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts public function
   - Expected: has_pub is true
   - Expected: has_fn is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts public function")
val source = "pub fn parse(source: text) -> Result:"
val has_pub = source.starts_with("pub ")
val has_fn = source.contains("fn ")
expect(has_pub).to_equal(true)
expect(has_fn).to_equal(true)
```

</details>

#### extracts private function

- extracts private function
   - Expected: has_pub is false
   - Expected: has_fn is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts private function")
val source = "fn helper() -> text:"
val has_pub = source.starts_with("pub ")
val has_fn = source.starts_with("fn ")
expect(has_pub).to_equal(false)
expect(has_fn).to_equal(true)
```

</details>

#### extracts exported function as public

- extracts exported function as public
   - Expected: is_exported is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts exported function as public")
val exports = ["parse", "Token"]
val name = "parse"
var is_exported = false
for e in exports:
    if e == name:
        is_exported = true
expect(is_exported).to_equal(true)
```

</details>

#### extracts internal_export as friend-visible

- extracts internal_export as friend-visible
   - Expected: is_internal is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts internal_export as friend-visible")
val internal_exports = ["Builder"]
val name = "Builder"
var is_internal = false
for e in internal_exports:
    if e == name:
        is_internal = true
expect(is_internal).to_equal(true)
```

</details>

#### extracts pub(friend) function

- extracts pub(friend) function
   - Expected: has_friend is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts pub(friend) function")
val source = "pub(friend) fn lower() -> MirModule:"
val has_friend = source.starts_with("pub(friend)")
expect(has_friend).to_equal(true)
```

</details>

#### extracts pub(package) function

- extracts pub(package) function
   - Expected: has_package is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts pub(package) function")
val source = "pub(package) fn validate() -> bool:"
val has_package = source.starts_with("pub(package)")
expect(has_package).to_equal(true)
```

</details>

#### extracts struct declarations

- extracts struct declarations
   - Expected: has_struct is true
   - Expected: has_pub is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts struct declarations")
val source = "pub struct Point:"
val has_struct = source.contains("struct ")
val has_pub = source.starts_with("pub ")
expect(has_struct).to_equal(true)
expect(has_pub).to_equal(true)
```

</details>

#### extracts enum declarations

- extracts enum declarations
   - Expected: has_enum is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts enum declarations")
val source = "enum Color:"
val has_enum = source.starts_with("enum ")
expect(has_enum).to_equal(true)
```

</details>

#### extracts trait declarations

- extracts trait declarations
   - Expected: has_trait is true
   - Expected: has_pub is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts trait declarations")
val source = "pub trait Printable:"
val has_trait = source.contains("trait ")
val has_pub = source.starts_with("pub ")
expect(has_trait).to_equal(true)
expect(has_pub).to_equal(true)
```

</details>

### Visibility Filtering

#### public filter shows only P symbols

- public filter shows only P symbols
   - Expected: pub_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("public filter shows only P symbols")
val visibilities = ["P", "-"]
var pub_count: i64 = 0
for v in visibilities:
    if v == "P":
        pub_count = pub_count + 1
expect(pub_count).to_equal(1)
```

</details>

#### all filter shows everything

- all filter shows everything


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all filter shows everything")
val visibilities = ["P", "-", "F", "I"]
expect(visibilities.len()).to_be_greater_than(1)
```

</details>

### API Tool Helpers

#### extract_fn_name from simple signature

- extract_fn_name from simple signature
   - Expected: name equals `parse`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extract_fn_name from simple signature")
val line = "fn parse(source: text) -> Result:"
# Extract function name: skip "fn " and take until "("
val after_fn = line.substring(3)
val paren_idx = after_fn.index_of("(")
val name = after_fn.substring(0, paren_idx)
expect(name).to_equal("parse")
```

</details>

#### extract_fn_name from method signature

- extract_fn_name from method signature
   - Expected: name equals `move`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extract_fn_name from method signature")
val line = "me move(dx: i64):"
# Extract method name: skip "me " and take until "("
val after_me = line.substring(3)
val paren_idx = after_me.index_of("(")
val name = after_me.substring(0, paren_idx)
expect(name).to_equal("move")
```

</details>

#### extract_type_name from struct

- extract_type_name from struct
   - Expected: name equals `Point`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extract_type_name from struct")
val after_kw = "Point:"
val colon_idx = after_kw.index_of(":")
val name = after_kw.substring(0, colon_idx)
expect(name).to_equal("Point")
```

</details>

#### extract_type_name with generic

- extract_type_name with generic
   - Expected: name equals `List`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extract_type_name with generic")
val after_kw = "List<T>:"
val angle_idx = after_kw.index_of("<")
val colon_idx = after_kw.index_of(":")
var end_idx = colon_idx
if angle_idx > 0 and angle_idx < colon_idx:
    end_idx = angle_idx
val name = after_kw.substring(0, end_idx)
expect(name).to_equal("List")
```

</details>

#### compute_visibility for exported symbol

- compute_visibility for exported symbol
   - Expected: vis equals `P`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compute_visibility for exported symbol")
val exports = ["parse", "Token"]
val internal_exports: [text] = []
val name = "parse"
var vis = "-"
for e in exports:
    if e == name:
        vis = "P"
for e in internal_exports:
    if e == name:
        vis = "F"
expect(vis).to_equal("P")
```

</details>

#### compute_visibility for internal_export symbol

- compute_visibility for internal_export symbol
   - Expected: vis equals `F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compute_visibility for internal_export symbol")
val exports: [text] = []
val internal_exports = ["Builder"]
val name = "Builder"
var vis = "-"
for e in exports:
    if e == name:
        vis = "P"
for e in internal_exports:
    if e == name:
        vis = "F"
expect(vis).to_equal("F")
```

</details>

#### compute_visibility for private symbol

- compute_visibility for private symbol
   - Expected: vis equals `-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compute_visibility for private symbol")
val exports = ["parse"]
val internal_exports = ["Builder"]
val name = "helper"
var vis = "-"
for e in exports:
    if e == name:
        vis = "P"
for e in internal_exports:
    if e == name:
        vis = "F"
expect(vis).to_equal("-")
```

</details>

### Type Domain Path Normalization

#### normalizes bare type name to default type domain

- normalizes bare type name to default type domain
   - Expected: normalized equals `src/type/simple_lang/I64.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes bare type name to default type domain")
val normalized = normalize_type_api_path("I64")
expect(normalized).to_equal("src/type/simple_lang/I64.spl")
```

</details>

#### normalizes owned-domain import path to type directory

- normalizes owned-domain import path to type directory
   - Expected: normalized equals `src/type/simple_lang/I64.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes owned-domain import path to type directory")
val normalized = normalize_type_api_path("simple-lang/I64")
expect(normalized).to_equal("src/type/simple_lang/I64.spl")
```

</details>

#### preserves nested owned-domain path segments

- preserves nested owned-domain path segments
   - Expected: normalized equals `src/type/simple_lang/math/F64.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves nested owned-domain path segments")
val normalized = normalize_type_api_path("simple-lang/math/F64")
expect(normalized).to_equal("src/type/simple_lang/math/F64.spl")
```

</details>

#### does not rewrite dotted module paths

- does not rewrite dotted module paths
   - Expected: normalized equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rewrite dotted module paths")
val normalized = normalize_type_api_path("compiler.frontend.parser_types")
expect(normalized).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/api_tool_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Symbol Extraction Heuristic, Visibility Filtering, API Tool Helpers, Type Domain Path Normalization.
- Symbol Extraction Heuristic
- Visibility Filtering
- API Tool Helpers
- Type Domain Path Normalization

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
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

- Canonical SPipe generation for source `6f303f603b36b90b8052627dbeafa3cfa57d4ec91e619e0955f2783f87c3bcc9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6f303f603b36b90b8052627dbeafa3cfa57d4ec91e619e0955f2783f87c3bcc9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6f303f603b36b90b8052627dbeafa3cfa57d4ec91e619e0955f2783f87c3bcc9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/mcp_unit/api_tool_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/api_tool_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/api_tool_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/api_tool_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/api_tool_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/api_tool_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts public function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/api_tool_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts private function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/api_tool_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts exported function as public' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
