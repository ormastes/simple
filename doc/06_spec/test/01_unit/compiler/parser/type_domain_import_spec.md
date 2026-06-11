# Type Domain Import Parsing Specification

> <details>

<!-- sdn-diagram:id=type_domain_import_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=type_domain_import_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

type_domain_import_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=type_domain_import_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Domain Import Parsing Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/type_domain_import_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### type domain imports

#### parses bare import keyword as use import

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decl = parse_first_import("import I64\n")
expect(decl_get_tag(decl)).to_equal(DECL_USE)
expect(decl_get_name(decl)).to_equal("I64")
expect(decl_get_imports(decl).len()).to_equal(0)
```

</details>

#### parses explicit owned-domain import with slash syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decl = parse_first_import("import simple-lang/I64\n")
expect(decl_get_name(decl)).to_equal("simple-lang/I64")
```

</details>

#### parses explicit owned-domain import with nested module path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decl = parse_first_import("import simple-lang/math.F64\n")
expect(decl_get_name(decl)).to_equal("simple-lang/math.F64")
```

</details>

#### keeps relative imports unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decl = parse_first_import("import .local_value\n")
expect(decl_get_name(decl)).to_equal(".local_value")
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
