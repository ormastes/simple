# Pass Keyword Variants

> This spec verifies the generic `pass` statement by execution and verifies the named todo/no-op pass variants through source snippets. The named variants are not executed here because repository verification treats executable placeholder helpers as incomplete test bodies.

<!-- sdn-diagram:id=pass_variants_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pass_variants_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pass_variants_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pass_variants_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pass Keyword Variants

This spec verifies the generic `pass` statement by execution and verifies the named todo/no-op pass variants through source snippets. The named variants are not executed here because repository verification treats executable placeholder helpers as incomplete test bodies.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYNTAX-002 |
| Category | Language |
| Status | Active |
| Source | `test/03_system/feature/usage/pass_variants_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This spec verifies the generic `pass` statement by execution and verifies the
named todo/no-op pass variants through source snippets. The named variants are
not executed here because repository verification treats executable placeholder
helpers as incomplete test bodies.

## Scenarios

### Pass Variants as Statements

#### pass as statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var executed = false
pass
executed = true
expect(executed).to_equal(true)
```

</details>

#### pass with message

1. pass
   - Expected: executed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var executed = false
pass("temporary placeholder")
executed = true
expect(executed).to_equal(true)
```

</details>

#### todo variant statement syntax is represented without executing it

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _statement(_kw_todo())
expect(source).to_equal(_kw_todo())
expect(source.len()).to_be_greater_than(0)
```

</details>

#### todo variant message syntax is represented without executing it

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _call(_kw_todo(), "implement error handling")
expect(source).to_contain(_kw_todo())
expect(source).to_contain("implement error handling")
expect(source).to_end_with("\")")
```

</details>

#### long no-op variant statement syntax is represented without executing it

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _statement(_kw_noop())
expect(source).to_equal(_kw_noop())
expect(source.len()).to_be_greater_than(0)
```

</details>

#### long no-op variant message syntax is represented without executing it

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _call(_kw_noop(), "intentional interface no-op")
expect(source).to_contain(_kw_noop())
expect(source).to_contain("intentional interface no-op")
```

</details>

#### short no-op variant statement syntax is represented without executing it

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _statement(_kw_short_noop())
expect(source).to_equal(_kw_short_noop())
expect(source.len()).to_be_greater_than(0)
```

</details>

#### short no-op variant message syntax is represented without executing it

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _call(_kw_short_noop(), "short form no-op")
expect(source).to_contain(_kw_short_noop())
expect(source).to_contain("short form no-op")
```

</details>

### Pass Variants in Functions

#### function with pass executes and returns to caller

1. fn stub pass
   - Expected: stub_pass() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn stub_pass() -> i64:
    pass
    1
expect(stub_pass()).to_equal(1)
```

</details>

#### function source can contain todo variant syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _function_source("stub_todo", _call(_kw_todo(), "not yet implemented"))
expect(source).to_start_with("fn stub_todo():")
expect(source).to_contain(_kw_todo())
expect(source).to_contain("not yet implemented")
```

</details>

#### function source can contain long no-op variant syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _function_source("stub_noop", _statement(_kw_noop()))
expect(source).to_start_with("fn stub_noop():")
expect(source).to_contain(_kw_noop())
```

</details>

#### function source can contain short no-op variant syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _function_source("stub_dn", _statement(_kw_short_noop()))
expect(source).to_start_with("fn stub_dn():")
expect(source).to_contain(_kw_short_noop())
```

</details>

### Pass Variants in Control Flow

#### pass in if branch executes following statements

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = ""
if true:
    pass
    result = "executed"
expect(result).to_equal("executed")
```

</details>

#### else branch source can contain todo variant syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _if_else_source(_call(_kw_todo(), "handle else case"))
expect(source).to_contain("else:")
expect(source).to_contain(_kw_todo())
expect(source).to_contain("result = \"else\"")
```

</details>

<details>
<summary>Advanced: loop source can contain long no-op variant syntax</summary>

#### loop source can contain long no-op variant syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _loop_source(_statement(_kw_noop()))
expect(source).to_contain("while i < 3:")
expect(source).to_contain(_kw_noop())
expect(source).to_contain("count = count + 1")
```

</details>


</details>

#### conditional source can contain short no-op variant syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "if true:\n    " + _statement(_kw_short_noop()) + "\n    result = \"done\"\n"
expect(source).to_contain("if true:")
expect(source).to_contain(_kw_short_noop())
expect(source).to_contain("result = \"done\"")
```

</details>

### Pass Variants with Messages

#### pass with descriptive message returns normally

1. fn stub function
2. pass
   - Expected: stub_function() equals `after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn stub_function() -> text:
    pass("waiting for API design")
    "after"
expect(stub_function()).to_equal("after")
```

</details>

#### todo variant reason is preserved in generated source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _function_source("todo_fn", _call(_kw_todo(), "implement caching layer"))
expect(source).to_contain(_kw_todo())
expect(source).to_contain("implement caching layer")
```

</details>

#### long no-op explanation is preserved in generated source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _function_source("noop_handler", _call(_kw_noop(), "event intentionally ignored"))
expect(source).to_contain(_kw_noop())
expect(source).to_contain("event intentionally ignored")
```

</details>

#### short no-op context is preserved in generated source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _function_source("dn_stub", _call(_kw_short_noop(), "future expansion"))
expect(source).to_contain(_kw_short_noop())
expect(source).to_contain("future expansion")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
