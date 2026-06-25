# Trait Desugar Specification

> <details>

<!-- sdn-diagram:id=trait_desugar_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=trait_desugar_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

trait_desugar_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=trait_desugar_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trait Desugar Specification

## Scenarios

### Trait Desugar

#### keeps trait to struct desugar entrypoint available

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = trait_desugar_source()

expect(source).to_contain("fn desugar_traits(source: text) -> text")
expect(source).to_contain("trait Name:")
expect(source).to_contain("struct Name:")
expect(source).to_contain("line.replace(\"trait \", \"struct \")")
```

</details>

#### keeps trait method conversion helpers available

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = trait_desugar_source()

expect(source).to_contain("fn _get_indent(line: text) -> text")
expect(source).to_contain("fn _method_to_fn_field(trimmed: text) -> text")
expect(source).to_contain("fn _extract_param_types(params_str: text) -> text")
expect(source).to_contain("method_name")
expect(source).to_contain("field_type")
```

</details>

#### keeps filtering of comments and default body lines available

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = trait_desugar_source()

expect(source).to_contain("trimmed.starts_with(\"#\")")
expect(source).to_contain("trimmed.starts_with(\"\\\"\\\"\\\"\")")
expect(source).to_contain("trimmed.starts_with(\"fn \")")
expect(source).to_contain("trimmed.starts_with(\"me \")")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/desugar/trait_desugar_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Trait Desugar

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
