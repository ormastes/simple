# Pure Parser Phase1 Specification

> <details>

<!-- sdn-diagram:id=pure_parser_phase1_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pure_parser_phase1_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pure_parser_phase1_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pure_parser_phase1_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Parser Phase1 Specification

## Scenarios

### Pure Parser Phase1

#### defines parsed result storage and accessors

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = simple_parser_api_source()

expect(src).to_contain("struct ParsedResult:")
expect(src).to_contain("flags: Dict<text, bool>")
expect(src).to_contain("options: Dict<text, text>")
expect(src).to_contain("positionals: [text]")
expect(src).to_contain("subcommand: text?")
expect(src).to_contain("subcommand_args: [text]")
expect(src).to_contain("fn get_flag(name: text) -> bool:")
expect(src).to_contain("fn get_option_or(name: text, default: text) -> text:")
expect(src).to_contain("fn positional_count() -> i64:")
```

</details>

#### defines builder methods for flags options positionals and subcommands

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = simple_parser_api_source()

expect(src).to_contain("struct SimpleParser:")
expect(src).to_contain("fn flag(name: text, short: text, description: text) -> SimpleParser:")
expect(src).to_contain("arg_kind: \"flag\"")
expect(src).to_contain("fn option(name: text, short: text, description: text, required: bool, default_value: text?) -> SimpleParser:")
expect(src).to_contain("fn required_option(name: text, short: text, description: text) -> SimpleParser:")
expect(src).to_contain("fn positional(name: text, description: text, required: bool) -> SimpleParser:")
expect(src).to_contain("fn subcommand_with_aliases(name: text, description: text, aliases: [text]) -> SimpleParser:")
expect(src).to_contain("fn no_auto_stage() -> SimpleParser:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/pure_parser_phase1_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Pure Parser Phase1

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
