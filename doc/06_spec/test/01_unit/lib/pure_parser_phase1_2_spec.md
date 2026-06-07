# Pure Parser Phase1 2 Specification

> <details>

<!-- sdn-diagram:id=pure_parser_phase1_2_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pure_parser_phase1_2_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pure_parser_phase1_2_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pure_parser_phase1_2_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Parser Phase1 2 Specification

## Scenarios

### Pure Parser Phase1 2

#### parses long flags options and subcommands without indentation globals

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = simple_parser_api_phase2_source()

expect(src).to_contain("fn parse(input_args: [text]) -> Result<ParsedResult, text>:")
expect(src).to_contain("for a in self.args:")
expect(src).to_contain("if a.arg_kind == \"flag\":")
expect(src).to_contain("if a.arg_kind == \"option\" and a.default_value.?:")
expect(src).to_contain("if not arg.starts_with(\"-\") and subcommand == nil")
expect(src).to_contain("val resolved = self.resolve_subcommand(arg)")
expect(src).to_contain("if arg.starts_with(\"--\"):")
expect(src).to_contain("if rest.contains(\"=\"):")
```

</details>

#### reports unknown and missing argument errors

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = simple_parser_api_phase2_source()

expect(src).to_contain("Unknown option: --")
expect(src).to_contain("requires a value")
expect(src).to_contain("Unknown argument: --")
expect(src).to_contain("Unknown flag: -")
expect(src).to_contain("Missing required option: --")
expect(src).to_contain("Missing required argument:")
expect(src).to_contain("Ok(ParsedResult(")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/pure_parser_phase1_2_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Pure Parser Phase1 2

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
