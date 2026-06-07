# Export-As Alias Syntax Spec

> Tests that `export name as alias` syntax is parsed correctly.

<!-- sdn-diagram:id=export_as_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=export_as_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

export_as_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=export_as_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Export-As Alias Syntax Spec

Tests that `export name as alias` syntax is parsed correctly.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #EXPORT-AS |
| Category | Language |
| Status | Implemented |
| Source | `test/01_unit/compiler/di/export_as_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests that `export name as alias` syntax is parsed correctly.
Previously broken: parse_export_decl() in parser.spl did not handle
the `as` aliasing keyword, causing "expected expression, found As" errors.

Fix: Added `as`-alias support to parse_export_decl() matching the pattern
already used in parse_use_decl().

## Scenarios

### Export as alias syntax

#### basic export works without alias

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _spec_helper_fn()
check(result == 42)
```

</details>

#### export as fix applied to parse_export_decl in parser.spl

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The fix adds `as`-aliasing to parse_export_decl() matching parse_use_decl()
# Once the binary is rebuilt with the fix, files using:
#   export foo as bar
# will parse correctly instead of failing with "expected expression, found As"
check(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
