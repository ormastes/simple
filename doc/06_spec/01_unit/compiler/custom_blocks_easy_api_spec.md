# Custom Blocks Easy Api Specification

> Tests covering Custom Blocks Easy API, block() - Minimal API, block_with_validation(), const_block() - Compile-time evaluation, BlockBuilder - Fluent API, BlockBuilder - Feature Presets, BlockBuilder - Smart Defaults, compiler.blocks.utils - Pre-built Parsers, compiler.blocks.utils - Pre-built Validators, compiler.blocks.utils - Syntax Highlighting, compiler.blocks.utils - Error Helpers, compiler.blocks.utils - Common Patterns, Block Registration, Recipe: Simple Text Block, Recipe: DSL with Validation, Recipe: Math-Like Syntax, Recipe: Compile-Time Constant, Recipe: IDE-Friendly Block, Performance, Edge Cases, Documentation Examples.

**Source:** `test/01_unit/compiler/custom_blocks_easy_api_spec.spl`

**Evidence scope:** The table counts authored scenarios, not a complete execution receipt. The unchanged suite contains local block API doubles. This repair verifies the actual production `strip_indent` owner in one original failed scenario and four new boundary scenarios; it does not certify the other block APIs or their performance. The original 46 passing scenarios were not rerun.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 51 | 51 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Custom Blocks Easy Api Specification

## Scenarios

### Custom Blocks Easy API

### block() - Minimal API

#### creates simple heredoc block with raw text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = create_simple_text_block("hello\nworld")
check_text(block.kind, "raw")
check_text(block.raw_text, "hello\nworld")
```

</details>

#### creates comment block that processes lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = create_simple_text_block("line 1\n# line 2")
check(block.raw_text.contains("# line 2"))
```

</details>

#### returns error for invalid syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = error_at_offset(3)
check_text(error, "error-at-3")
```

</details>

### block_with_validation()

#### validates block value after parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = create_validated_sql_block("select * from users")
check_text(block.validator_name, "simple_validator")
check(validate_sql_with_dialect(block.raw_text, "sqlite"))
```

</details>

### const_block() - Compile-time evaluation

#### evaluates regex at compile time

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = create_regex_block("/[a-z]+/")
check_text(block.validator_name, "regex")
check(validate_regex_pattern(block.raw_text))
```

</details>

### BlockBuilder - Fluent API

#### creates block with chained methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = BlockBuilder.create()
builder.raw_text = "alpha"
builder.set_validator("simple_validator")
val block = builder.build()
check_text(block.raw_text, "alpha")
check_text(block.validator_name, "simple_validator")
```

</details>

#### enables math features for tensor block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = create_tensor_block("tensor block")
check_text(block.kind, "math")
```

</details>

#### adds validation with simple_validator

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = BlockBuilder.create()
builder.raw_text = "json"
builder.set_validator("simple_validator")
val block = builder.build()
check_text(block.validator_name, "simple_validator")
```

</details>

#### provides IDE support with highlighter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = create_ide_block("highlight me")
check(block.highlight_enabled)
```

</details>

### BlockBuilder - Feature Presets

#### enables all math features with preset

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = BlockBuilder.create()
builder.enable_math_features()
val block = builder.build()
check_text(block.kind, "math")
```

</details>

#### enables pipeline operators with preset

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = BlockBuilder.create()
builder.enable_pipeline_operators()
val block = builder.build()
check_text(block.kind, "pipeline")
```

</details>

### BlockBuilder - Smart Defaults

#### uses raw text mode by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = BlockBuilder.create().build()
check_text(block.kind, "raw")
```

</details>

#### has no syntax features enabled by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = BlockBuilder.create().build()
check(block.features.len() >= 1)
```

</details>

#### provides pass-through validator by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = BlockBuilder.create().build()
check_text(block.validator_name, "")
```

</details>

### compiler.blocks.utils - Pre-built Parsers

#### parses JSON with utility function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(parse_json_like("{\"name\": \"Alice\"}"))
```

</details>

#### parses YAML with utility function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(parse_yaml_like("name: Alice\nage: 30"))
```

</details>

#### parses TOML with utility function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(parse_toml_like("name = \"Alice\""))
```

</details>

#### parses CSV with utility function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(parse_csv_like("a,b,c"))
```

</details>

### compiler.blocks.utils - Pre-built Validators

#### validates JSON structure

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(validate_json_structure("{\"name\": \"Alice\"}"))
```

</details>

#### validates regex pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(validate_regex_pattern("/abc/"))
```

</details>

#### validates SQL with dialect

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(validate_sql_with_dialect("select * from users", "postgres"))
```

</details>

### compiler.blocks.utils - Syntax Highlighting

#### highlights keywords in text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(highlight_keywords("block builder validator") >= 3)
```

</details>

#### highlights strings in text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(highlight_strings("value = \"text\""))
```

</details>

#### highlights comments in text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(highlight_comments("# comment"))
```

</details>

#### highlights numbers in text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(highlight_numbers("1 2 3"))
```

</details>

### compiler.blocks.utils - Error Helpers

#### creates error at specific offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(error_at_offset(12), "error-at-12")
```

</details>

#### creates error with span

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(error_with_span("block.spl", 3, 8), "block.spl:3:8")
```

</details>

#### converts string errors to BlockError array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = string_errors_to_array("first\nsecond")
check(errors.len() == 2)
```

</details>

### compiler.blocks.utils - Common Patterns

#### interpolates variables in text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(interpolate_variables("Ada"), "Hello, Ada")
```

</details>

#### strips common indentation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(strip_common_indentation("  one\n  two"), "one\ntwo")
```

</details>

#### preserves relative indentation with a later smaller minimum

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(strip_common_indentation("    deep\n  shallow"), "  deep\nshallow")
```

</details>

#### preserves blank lines and trailing spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(strip_common_indentation("\n  one  \n    two\n"), "\none  \n  two\n")
```

</details>

#### preserves Unicode payload and leaves zero-indented content intact

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(strip_common_indentation("  λ\n  한글"), "λ\n한글")
check_text(strip_common_indentation("one\n  two"), "one\n  two")
```

</details>

#### preserves empty content

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(strip_common_indentation(""), "")
```

</details>

#### normalizes line endings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(normalize_line_endings("line1\r\nline2"), "normalized-line-endings")
```

</details>

### Block Registration

#### registers and unregisters blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_registered_blocks()
register_block("alpha")
register_block("beta")
unregister_block("alpha")
val names = list_registered_blocks()
check(names.len() == 1)
check_text(names[0], "beta")
```

</details>

#### lists all registered blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_registered_blocks()
register_block("one")
register_block("two")
val names = list_registered_blocks()
check(names.len() == 2)
```

</details>

#### provides scoped registration for testing

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_registered_blocks()
register_block("scoped")
check(list_registered_blocks().contains("scoped"))
clear_registered_blocks()
check(list_registered_blocks().len() == 0)
```

</details>

### Recipe: Simple Text Block

#### creates heredoc with trimming

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = create_simple_text_block("  line  ")
check(block.raw_text.starts_with("  "))
```

</details>

### Recipe: DSL with Validation

#### creates validated SQL block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = create_validated_sql_block("select id from users")
check_text(block.validator_name, "simple_validator")
```

</details>

### Recipe: Math-Like Syntax

#### creates tensor block with math operators

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = create_tensor_block("x + y")
check_text(block.kind, "math")
```

</details>

### Recipe: Compile-Time Constant

#### compiles regex at compile time

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = create_regex_block("/[0-9]+/")
check(block.raw_text.contains("0"))
```

</details>

### Recipe: IDE-Friendly Block

#### provides full IDE support

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = create_ide_block("suggestions")
check(block.highlight_enabled)
```

</details>

### Performance

#### builder compiles away at build time

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = BlockBuilder.create()
val block = builder.build()
check_text(block.kind, "raw")
```

</details>

#### simple_parser unwraps to full signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = BlockBuilder.create()
builder.raw_text = "signature"
builder.set_validator("pass_through")
val block = builder.build()
check_text(block.validator_name, "pass_through")
```

</details>

### Edge Cases

#### handles empty payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = create_simple_text_block("")
check_text(block.raw_text, "")
```

</details>

#### handles unicode in payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = create_simple_text_block("héllo")
check(block.raw_text.contains("é"))
```

</details>

#### handles nested braces in raw mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = create_simple_text_block("{{value}}")
check(block.raw_text.contains("{{"))
```

</details>

### Documentation Examples

#### minimal example from README

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = create_simple_text_block("readme example")
check_text(block.kind, "raw")
```

</details>

#### builder example from README

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = BlockBuilder.create()
builder.raw_text = "builder example"
builder.enable_math_features()
val block = builder.build()
check_text(block.kind, "math")
```

</details>

#### feature preset example from README

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = BlockBuilder.create()
builder.enable_pipeline_operators()
val block = builder.build()
check_text(block.kind, "pipeline")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/compiler/custom_blocks_easy_api_spec.spl` |
| Updated | 2026-10-10 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Custom Blocks Easy API, block() - Minimal API, block_with_validation(), const_block() - Compile-time evaluation, BlockBuilder - Fluent API, BlockBuilder - Feature Presets, BlockBuilder - Smart Defaults, compiler.blocks.utils - Pre-built Parsers, compiler.blocks.utils - Pre-built Validators, compiler.blocks.utils - Syntax Highlighting, compiler.blocks.utils - Error Helpers, compiler.blocks.utils - Common Patterns, Block Registration, Recipe: Simple Text Block, Recipe: DSL with Validation, Recipe: Math-Like Syntax, Recipe: Compile-Time Constant, Recipe: IDE-Friendly Block, Performance, Edge Cases, Documentation Examples.
- Custom Blocks Easy API
- block() - Minimal API
- block_with_validation()
- const_block() - Compile-time evaluation
- BlockBuilder - Fluent API
- BlockBuilder - Feature Presets
- BlockBuilder - Smart Defaults
- compiler.blocks.utils - Pre-built Parsers
- compiler.blocks.utils - Pre-built Validators
- compiler.blocks.utils - Syntax Highlighting
- compiler.blocks.utils - Error Helpers
- compiler.blocks.utils - Common Patterns
- Block Registration
- Recipe: Simple Text Block
- Recipe: DSL with Validation
- Recipe: Math-Like Syntax
- Recipe: Compile-Time Constant
- Recipe: IDE-Friendly Block
- Performance
- Edge Cases
- Documentation Examples

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 51 |
| Active scenarios | 51 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

## Indentation setup ownership

The helper `strip_common_indentation` delegates to `compiler.blocks.blocks.text_transforms.strip_indent`. It does not implement a separate local dedent algorithm.
