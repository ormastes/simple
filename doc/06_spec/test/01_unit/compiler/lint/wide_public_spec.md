# Wide Public Lint Specification

> Tests the W0404 lint that detects modules exporting too many public symbols. The default threshold is 30.

<!-- sdn-diagram:id=wide_public_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wide_public_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wide_public_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wide_public_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wide Public Lint Specification

Tests the W0404 lint that detects modules exporting too many public symbols. The default threshold is 30.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LINT-W0404 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/compiler/lint/wide_public_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the W0404 lint that detects modules exporting too many public symbols.
The default threshold is 30.

## Key Concepts

| Concept | Description |
|---------|-------------|
| W0404 | Module exports more than threshold symbols |
| DEFAULT_PUBLIC_THRESHOLD | 30 — configurable per-call |
| File filtering | __init__.spl and mod.spl are skipped |

## Scenarios

### W0404 — Wide Public Lint — Default Threshold

#### DEFAULT_PUBLIC_THRESHOLD is 30

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DEFAULT_PUBLIC_THRESHOLD).to_equal(30)
```

</details>

### W0404 — Under threshold

#### when module exports fewer than threshold symbols

#### emits no warnings

1. ast reset
   - Expected: ws.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val ex = make_export(gen_names("fn", 10))
val ws = check_wide_public([ex])
expect(ws.len()).to_equal(0)
```

</details>

#### when module exports exactly threshold symbols

#### emits no warnings

1. ast reset
   - Expected: ws.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val ex = make_export(gen_names("fn", 30))
val ws = check_wide_public([ex])
expect(ws.len()).to_equal(0)
```

</details>

#### when module has no exports

#### emits no warnings

1. ast reset
   - Expected: ws.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val d = make_dummy_fn("internal_fn")
val ws = check_wide_public([d])
expect(ws.len()).to_equal(0)
```

</details>

### W0404 — Over threshold

#### when module exports more than default threshold

#### emits W0404 warning

1. ast reset
   - Expected: ws.len() equals `1`
   - Expected: ws[0].code equals `W0404`
   - Expected: ws[0].export_count equals `31`
   - Expected: ws[0].threshold equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val ex = make_export(gen_names("sym", 31))
val ws = check_wide_public([ex])
expect(ws.len()).to_equal(1)
expect(ws[0].code).to_equal("W0404")
expect(ws[0].export_count).to_equal(31)
expect(ws[0].threshold).to_equal(30)
```

</details>

#### when exports spread across multiple export decls

#### counts total unique names

1. ast reset
   - Expected: ws.len() equals `1`
   - Expected: ws[0].export_count equals `35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val ex1 = make_export(gen_names("a", 20))
val ex2 = make_export(gen_names("b", 15))
val ws = check_wide_public([ex1, ex2])
expect(ws.len()).to_equal(1)
expect(ws[0].export_count).to_equal(35)
```

</details>

#### when duplicate names across exports

#### counts unique names only

1. ast reset
   - Expected: ws.len() equals `1`
   - Expected: ws[0].export_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val names1 = ["foo", "bar", "baz"]
val names2 = ["foo", "qux"]
val ex1 = make_export(names1)
val ex2 = make_export(names2)
val ws = check_wide_public_with_threshold([ex1, ex2], 3)
expect(ws.len()).to_equal(1)
expect(ws[0].export_count).to_equal(4)
```

</details>

### W0404 — Custom threshold

#### when custom threshold is lower

#### flags smaller modules

1. ast reset
   - Expected: ws.len() equals `1`
   - Expected: ws[0].threshold equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val ex = make_export(gen_names("sym", 5))
val ws = check_wide_public_with_threshold([ex], 4)
expect(ws.len()).to_equal(1)
expect(ws[0].threshold).to_equal(4)
```

</details>

#### when custom threshold is higher

#### allows larger modules

1. ast reset
   - Expected: ws.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val ex = make_export(gen_names("sym", 50))
val ws = check_wide_public_with_threshold([ex], 100)
expect(ws.len()).to_equal(0)
```

</details>

### W0404 — File-based filtering

#### when file is __init__.spl

#### skips the check

1. ast reset
   - Expected: ws.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val ex = make_export(gen_names("sym", 50))
val ws = check_wide_public_file([ex], "src/lib/common/__init__.spl")
expect(ws.len()).to_equal(0)
```

</details>

#### when file is mod.spl

#### skips the check

1. ast reset
   - Expected: ws.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val ex = make_export(gen_names("sym", 50))
val ws = check_wide_public_file([ex], "src/lib/net/tcp/mod.spl")
expect(ws.len()).to_equal(0)
```

</details>

#### when file is a regular module

#### applies the check

1. ast reset
   - Expected: ws.len() equals `1`
   - Expected: ws[0].code equals `W0404`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val ex = make_export(gen_names("sym", 31))
val ws = check_wide_public_file([ex], "src/lib/net/tcp/connection.spl")
expect(ws.len()).to_equal(1)
expect(ws[0].code).to_equal("W0404")
```

</details>

### W0404 — Warning format

#### warning has correct severity

1. ast reset
   - Expected: ws[0].severity equals `WARNING`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val ex = make_export(gen_names("sym", 31))
val ws = check_wide_public([ex])
expect(ws[0].severity).to_equal("WARNING")
```

</details>

#### fmt includes counts

1. ast reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val ex = make_export(gen_names("sym", 31))
val ws = check_wide_public([ex])
val msg = ws[0].fmt()
expect(msg).to_contain("31 symbols")
expect(msg).to_contain("threshold 30")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
