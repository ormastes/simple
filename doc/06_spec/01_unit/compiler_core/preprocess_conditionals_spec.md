# Preprocess Conditionals Specification

> <details>

<!-- sdn-diagram:id=preprocess_conditionals_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=preprocess_conditionals_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

preprocess_conditionals_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=preprocess_conditionals_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Preprocess Conditionals Specification

## Scenarios

### Preprocess Conditionals

#### should expose conditional preprocessing through parser entrypoints

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parser_src = read_source("src/compiler/10.frontend/core/parser.spl")
val init_src = read_source("src/compiler/10.frontend/core/__init__.spl")
expect(parser_src.contains("use compiler.frontend.core.parser_preprocessor")).to_equal(true)
expect(parser_src.contains("val preprocessed = _pp_preprocess_conditionals(source)")).to_equal(true)
expect(parser_src.contains("export _pp_preprocess_conditionals, preprocess_conditionals")).to_equal(true)
expect(init_src.contains("export preprocess_conditionals")).to_equal(true)
```

</details>

#### should recognize when elif else and end directives

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/parser_preprocessor.spl")
expect(src.contains("fn _pp_preprocess_conditionals(source: text) -> text")).to_equal(true)
expect(src.contains("val is_when = trimmed.starts_with(\"@when(\")")).to_equal(true)
expect(src.contains("val is_elif = trimmed.starts_with(\"@elif(\")")).to_equal(true)
expect(src.contains("val is_else = trimmed == \"@else\" or trimmed == \"@else:\"")).to_equal(true)
expect(src.contains("val is_end = trimmed == \"@end\"")).to_equal(true)
```

</details>

#### should preserve diagnostic line count for inactive branches

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/parser_preprocessor.spl")
expect(src.contains("if active:")).to_equal(true)
expect(src.contains("out_lines.push(line)")).to_equal(true)
expect(src.contains("Keep line count stable for diagnostics")).to_equal(true)
expect(src.contains("out_lines.push(\"\")")).to_equal(true)
```

</details>

#### should honor target os and arch environment overrides

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/cfg_platform.spl")
expect(src.contains("cfg_env(\"SIMPLE_TARGET_OS\")")).to_equal(true)
expect(src.contains("cfg_env(\"SIMPLE_TARGET_ARCH\")")).to_equal(true)
expect(src.contains("fn cfg_detect_os() -> text")).to_equal(true)
expect(src.contains("fn cfg_detect_arch() -> text")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/preprocess_conditionals_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Preprocess Conditionals

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
