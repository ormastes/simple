# treesitter_error_recovery_spec

> TreeSitter Error Recovery Specification

<!-- sdn-diagram:id=treesitter_error_recovery_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_error_recovery_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_error_recovery_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=treesitter_error_recovery_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# treesitter_error_recovery_spec

TreeSitter Error Recovery Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-ERR-001 |
| Category | Compiler \| Parser |
| Status | Active |
| Source | `test/01_unit/compiler/parser/treesitter_error_recovery_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

TreeSitter Error Recovery Specification

@cover src/compiler/10.frontend/treesitter.spl 80%

Tests error recovery: parsing continues after syntax errors.

## Scenarios

### TreeSitter Error Recovery

#### recovers after malformed function

1. var ts = TreeSitter new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn broken(:\n    1\n\nfn valid():\n    2\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
# Should still find the valid function after error recovery
expect(outline.functions.len()).to_be_greater_than(0)
```

</details>

#### parses valid code after syntax error

1. var ts = TreeSitter new
   - Expected: outline.functions.len() equals `1`
   - Expected: outline.functions[0].name equals `good`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "class :\n\nfn good():\n    42\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
expect(outline.functions.len()).to_equal(1)
expect(outline.functions[0].name).to_equal("good")
```

</details>

#### collects errors from malformed source

1. var ts = TreeSitter new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn ():\n    pass\n"
var ts = TreeSitter.new(src)
val outline = ts.parse_outline()
expect(outline.errors.len()).to_be_greater_than(0)
```

</details>

#### produces empty outline for gibberish

1. var ts = TreeSitter new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts = TreeSitter.new("!@#$%^&*")
val outline = ts.parse_outline()
expect(outline.errors.len()).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
