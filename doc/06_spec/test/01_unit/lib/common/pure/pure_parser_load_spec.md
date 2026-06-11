# Pure Parser Load Specification

> <details>

<!-- sdn-diagram:id=pure_parser_load_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pure_parser_load_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pure_parser_load_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pure_parser_load_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Parser Load Specification

## Scenarios

### Pure Parser Load

#### selects runtime pure and auto parser modes from the environment

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = common_parser_loader_source()

expect(src).to_contain("enum ParserMode:")
expect(src).to_contain("Runtime")
expect(src).to_contain("Pure")
expect(src).to_contain("Auto")
expect(src).to_contain("val mode_str = env_get(\"SIMPLE_PURE_PARSER\")")
expect(src).to_contain("if mode_str == \"1\" or mode_str == \"true\":")
expect(src).to_contain("elif mode_str == \"0\" or mode_str == \"false\":")
expect(src).to_contain("elif mode_str == \"auto\":")
expect(src).to_contain("ParserMode.Runtime")
```

</details>

#### falls back when the pure parser SMF artifact is unavailable

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = common_parser_loader_source()
val init_src = common_cli_init_source()

expect(src).to_contain("fn should_use_pure_parser() -> bool:")
expect(src).to_contain("val smf_path = \"build/bootstrap/parser_stage2.smf\"")
expect(src).to_contain("if file_exists(smf_path):")
expect(src).to_contain("Falling back to runtime parser")
expect(src).to_contain("file_exists(\"build/bootstrap/parser_stage2.smf\")")
expect(src).to_contain("fn get_parser_info() -> text:")
expect(src).to_contain("Pure Simple Parser (SMF)")
expect(src).to_contain("Runtime Parser (built-in)")
expect(init_src).to_contain("export ParserMode, get_parser_mode, should_use_pure_parser")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/pure_parser_load_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Pure Parser Load

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
