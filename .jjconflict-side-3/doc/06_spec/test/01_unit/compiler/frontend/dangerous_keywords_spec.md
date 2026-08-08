# Dangerous Keywords Specification

> Tests the extensible "dangerous keyword" registry. Any identifier registered in DANGEROUS_KEYWORDS must be called with a required comment string argument; omitting the comment emits a REQC002 warning. The registry ships with at least `dangerous_token_but_needs` and `loss` pre-registered.

<!-- sdn-diagram:id=dangerous_keywords_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dangerous_keywords_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dangerous_keywords_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dangerous_keywords_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dangerous Keywords Specification

Tests the extensible "dangerous keyword" registry. Any identifier registered in DANGEROUS_KEYWORDS must be called with a required comment string argument; omitting the comment emits a REQC002 warning. The registry ships with at least `dangerous_token_but_needs` and `loss` pre-registered.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #REQC-AC3 |
| Category | Compiler \| Frontend \| Parser |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/compiler/frontend/dangerous_keywords_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the extensible "dangerous keyword" registry. Any identifier registered in
DANGEROUS_KEYWORDS must be called with a required comment string argument;
omitting the comment emits a REQC002 warning. The registry ships with at least
`dangerous_token_but_needs` and `loss` pre-registered.

## Syntax

```simple
# Required form — comment arg mandatory
dangerous_token_but_needs("reason for using this dangerous construct")
dangerous_token_but_needs("reason", [SymbolRef1, SymbolRef2])
loss("reason: gradient accumulation intentional")

# Missing comment — emits REQC002 warning
dangerous_token_but_needs
dangerous_token_but_needs()
loss
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| REQC002 | Warning code for dangerous keyword used without a comment string |
| DANGEROUS_KEYWORDS | Extensible list of identifier strings that require comments |
| is_dangerous_keyword | Predicate checked by parser when encountering an identifier |
| DangerousKeywordRef | Struct holding a symbol name referenced by a dangerous call |
| symbol_refs | Optional second argument listing symbols associated with the dangerous call |

## Scenarios

### dangerous_token_but_needs — required comment

#### when called without any argument

#### emits a REQC002 warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = collect_dangerous_warning("dangerous_token_but_needs", "")
expect(ws.len()).to_be_greater_than(0)
expect(has_reqc002(ws)).to_equal(true)
```

</details>

#### warning message names the keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = collect_dangerous_warning("dangerous_token_but_needs", "")
expect(ws[0]).to_contain("dangerous_token_but_needs")
```

</details>

#### when called with a non-empty comment string

#### does NOT emit a REQC002 warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = collect_dangerous_warning("dangerous_token_but_needs", "needed for ABI compat")
expect(ws.len()).to_equal(0)
```

</details>

#### when called with comment and symbol references

#### does NOT emit a warning (comment present)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = collect_dangerous_warning("dangerous_token_but_needs", "using Allocator reference")
expect(ws.len()).to_equal(0)
```

</details>

### loss — dangerous keyword outside ML block context

#### when loss is called without a comment

#### emits a REQC002 warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = collect_dangerous_warning("loss", "")
expect(ws.len()).to_be_greater_than(0)
expect(has_reqc002(ws)).to_equal(true)
```

</details>

#### when loss is called with a comment

#### does NOT emit a warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = collect_dangerous_warning("loss", "gradient accumulation intentional here")
expect(ws.len()).to_equal(0)
```

</details>

### is_dangerous_keyword — registry lookup

#### dangerous_token_but_needs is registered

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_dangerous_keyword_test("dangerous_token_but_needs")).to_equal(true)
```

</details>

#### loss is registered

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_dangerous_keyword_test("loss")).to_equal(true)
```

</details>

#### print is NOT registered

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_dangerous_keyword_test("print")).to_equal(false)
```

</details>

#### pass_todo is NOT in dangerous keywords registry

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_dangerous_keyword_test("pass_todo")).to_equal(false)
```

</details>

#### empty string is NOT registered

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_dangerous_keyword_test("")).to_equal(false)
```

</details>

#### partial match is NOT registered

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_dangerous_keyword_test("dangerous_token")).to_equal(false)
```

</details>

### dangerous keyword registry — custom extension

#### when a custom keyword is added to the registry

#### is_dangerous_keyword returns true for the new keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulate extending the registry
val extended = DANGEROUS_KEYWORDS_TEST + ["unsafe_gc_bypass"]
val found = _list_contains(extended, "unsafe_gc_bypass")
expect(found).to_equal(true)
```

</details>

#### warning is emitted when new keyword used without comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulate using the new keyword without a comment
val extended_check = _extended_should_warn(
    ["dangerous_token_but_needs", "loss", "unsafe_gc_bypass"],
    "unsafe_gc_bypass",
    ""
)
expect(extended_check).to_equal(true)
```

</details>

#### no warning when new keyword used with comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extended_check = _extended_should_warn(
    ["dangerous_token_but_needs", "loss", "unsafe_gc_bypass"],
    "unsafe_gc_bypass",
    "GC bypass approved for hot path"
)
expect(extended_check).to_equal(false)
```

</details>

### dangerous keyword — symbol reference parsing

#### zero symbol refs is valid when comment is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = collect_dangerous_warning("dangerous_token_but_needs", "only comment, no refs")
expect(ws.len()).to_equal(0)
```

</details>

#### parsed symbol refs are stored as DangerousKeywordRef list

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val refs = parse_symbol_refs_test(["Allocator", "MemPool"])
expect(refs.len()).to_equal(2)
expect(refs[0]).to_equal("Allocator")
expect(refs[1]).to_equal("MemPool")
```

</details>

#### no symbol refs returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val refs = parse_symbol_refs_test([])
expect(refs.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
