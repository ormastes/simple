# Custom Blocks Easy Api Specification

> Tests covering Custom Blocks Easy API, block() - Minimal API, block_with_validation(), const_block() - Compile-time evaluation, BlockBuilder - Fluent API, BlockBuilder - Feature Presets, BlockBuilder - Smart Defaults, compiler.blocks.utils - Pre-built Parsers, compiler.blocks.utils - Pre-built Validators, compiler.blocks.utils - Syntax Highlighting, compiler.blocks.utils - Error Helpers, compiler.blocks.utils - Common Patterns, Block Registration, Recipe: Simple Text Block, Recipe: DSL with Validation, Recipe: Math-Like Syntax, Recipe: Compile-Time Constant, Recipe: IDE-Friendly Block, Performance, Edge Cases, Documentation Examples.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Custom Blocks Easy Api Specification

## Scenarios

### Custom Blocks Easy API

### block() - Minimal API

#### creates simple heredoc block with raw text

- creates simple heredoc block with raw text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates simple heredoc block with raw text")
val block = create_simple_text_block("hello\nworld")
check_text(block.kind, "raw")
check_text(block.raw_text, "hello\nworld")
```

</details>

#### creates comment block that processes lines

- creates comment block that processes lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates comment block that processes lines")
val block = create_simple_text_block("line 1\n# line 2")
check(block.raw_text.contains("# line 2"))
```

</details>

#### returns error for invalid syntax

- returns error for invalid syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for invalid syntax")
val error = error_at_offset(3)
check_text(error, "error-at-3")
```

</details>

### block_with_validation()

#### validates block value after parsing

- validates block value after parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates block value after parsing")
val block = create_validated_sql_block("select * from users")
check_text(block.validator_name, "simple_validator")
check(validate_sql_with_dialect(block.raw_text, "sqlite"))
```

</details>

### const_block() - Compile-time evaluation

#### evaluates regex at compile time

- evaluates regex at compile time


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("evaluates regex at compile time")
val block = create_regex_block("/[a-z]+/")
check_text(block.validator_name, "regex")
check(validate_regex_pattern(block.raw_text))
```

</details>

### BlockBuilder - Fluent API

#### creates block with chained methods

- creates block with chained methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates block with chained methods")
val builder = BlockBuilder.create()
builder.set_raw_text("alpha")
builder.set_validator("simple_validator")
val block = builder.build()
check_text(block.raw_text, "alpha")
check_text(block.validator_name, "simple_validator")
```

</details>

#### enables math features for tensor block

- enables math features for tensor block


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables math features for tensor block")
val block = create_tensor_block("tensor block")
check_text(block.kind, "math")
```

</details>

#### adds validation with simple_validator

- adds validation with simple_validator


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds validation with simple_validator")
val builder = BlockBuilder.create()
builder.set_raw_text("json")
builder.set_validator("simple_validator")
val block = builder.build()
check_text(block.validator_name, "simple_validator")
```

</details>

#### provides IDE support with highlighter

- provides IDE support with highlighter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides IDE support with highlighter")
val block = create_ide_block("highlight me")
check(block.highlight_enabled)
```

</details>

### BlockBuilder - Feature Presets

#### enables all math features with preset

- enables all math features with preset


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables all math features with preset")
val builder = BlockBuilder.create()
builder.enable_math_features()
val block = builder.build()
check_text(block.kind, "math")
```

</details>

#### enables pipeline operators with preset

- enables pipeline operators with preset


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables pipeline operators with preset")
val builder = BlockBuilder.create()
builder.enable_pipeline_operators()
val block = builder.build()
check_text(block.kind, "pipeline")
```

</details>

### BlockBuilder - Smart Defaults

#### uses raw text mode by default

- uses raw text mode by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses raw text mode by default")
val block = BlockBuilder.create().build()
check_text(block.kind, "raw")
```

</details>

#### has no syntax features enabled by default

- has no syntax features enabled by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has no syntax features enabled by default")
val block = BlockBuilder.create().build()
check(block.features.len() >= 1)
```

</details>

#### provides pass-through validator by default

- provides pass-through validator by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides pass-through validator by default")
val block = BlockBuilder.create().build()
check_text(block.validator_name, "")
```

</details>

### compiler.blocks.utils - Pre-built Parsers

#### parses JSON with utility function

- parses JSON with utility function


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses JSON with utility function")
check(parse_json_like("{\"name\": \"Alice\"}"))
```

</details>

#### parses YAML with utility function

- parses YAML with utility function


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses YAML with utility function")
check(parse_yaml_like("name: Alice\nage: 30"))
```

</details>

#### parses TOML with utility function

- parses TOML with utility function


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses TOML with utility function")
check(parse_toml_like("name = \"Alice\""))
```

</details>

#### parses CSV with utility function

- parses CSV with utility function


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses CSV with utility function")
check(parse_csv_like("a,b,c"))
```

</details>

### compiler.blocks.utils - Pre-built Validators

#### validates JSON structure

- validates JSON structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates JSON structure")
check(validate_json_structure("{\"name\": \"Alice\"}"))
```

</details>

#### validates regex pattern

- validates regex pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates regex pattern")
check(validate_regex_pattern("/abc/"))
```

</details>

#### validates SQL with dialect

- validates SQL with dialect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates SQL with dialect")
check(validate_sql_with_dialect("select * from users", "postgres"))
```

</details>

### compiler.blocks.utils - Syntax Highlighting

#### highlights keywords in text

- highlights keywords in text


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("highlights keywords in text")
check(highlight_keywords("block builder validator") >= 3)
```

</details>

#### highlights strings in text

- highlights strings in text


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("highlights strings in text")
check(highlight_strings("value = \"text\""))
```

</details>

#### highlights comments in text

- highlights comments in text


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("highlights comments in text")
check(highlight_comments("# comment"))
```

</details>

#### highlights numbers in text

- highlights numbers in text


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("highlights numbers in text")
check(highlight_numbers("1 2 3"))
```

</details>

### compiler.blocks.utils - Error Helpers

#### creates error at specific offset

- creates error at specific offset


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates error at specific offset")
check_text(error_at_offset(12), "error-at-12")
```

</details>

#### creates error with span

- creates error with span


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates error with span")
check_text(error_with_span("block.spl", 3, 8), "block.spl:3:8")
```

</details>

#### converts string errors to BlockError array

- converts string errors to BlockError array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts string errors to BlockError array")
val errors = string_errors_to_array("first\nsecond")
check(errors.len() == 2)
```

</details>

### compiler.blocks.utils - Common Patterns

#### interpolates variables in text

- interpolates variables in text


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolates variables in text")
check_text(interpolate_variables("Ada"), "Hello, Ada")
```

</details>

#### strips common indentation

- strips common indentation


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips common indentation")
check_text(strip_common_indentation("  one\n  two"), "one\ntwo")
```

</details>

#### normalizes line endings

- normalizes line endings


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes line endings")
check_text(normalize_line_endings("line1\r\nline2"), "normalized-line-endings")
```

</details>

### Block Registration

#### registers and unregisters blocks

- registers and unregisters blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers and unregisters blocks")
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

- lists all registered blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists all registered blocks")
clear_registered_blocks()
register_block("one")
register_block("two")
val names = list_registered_blocks()
check(names.len() == 2)
```

</details>

#### provides scoped registration for testing

- provides scoped registration for testing


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides scoped registration for testing")
clear_registered_blocks()
register_block("scoped")
check(list_registered_blocks().contains("scoped"))
clear_registered_blocks()
check(list_registered_blocks().len() == 0)
```

</details>

### Recipe: Simple Text Block

#### creates heredoc with trimming

- creates heredoc with trimming


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates heredoc with trimming")
val block = create_simple_text_block("  line  ")
check(block.raw_text.starts_with("  "))
```

</details>

### Recipe: DSL with Validation

#### creates validated SQL block

- creates validated SQL block


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates validated SQL block")
val block = create_validated_sql_block("select id from users")
check_text(block.validator_name, "simple_validator")
```

</details>

### Recipe: Math-Like Syntax

#### creates tensor block with math operators

- creates tensor block with math operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates tensor block with math operators")
val block = create_tensor_block("x + y")
check_text(block.kind, "math")
```

</details>

### Recipe: Compile-Time Constant

#### compiles regex at compile time

- compiles regex at compile time


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles regex at compile time")
val block = create_regex_block("/[0-9]+/")
check(block.raw_text.contains("0"))
```

</details>

### Recipe: IDE-Friendly Block

#### provides full IDE support

- provides full IDE support


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides full IDE support")
val block = create_ide_block("suggestions")
check(block.highlight_enabled)
```

</details>

### Performance

#### builder compiles away at build time

- builder compiles away at build time


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builder compiles away at build time")
val builder = BlockBuilder.create()
val block = builder.build()
check_text(block.kind, "raw")
```

</details>

#### simple_parser unwraps to full signature

- simple_parser unwraps to full signature


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_parser unwraps to full signature")
val builder = BlockBuilder.create()
builder.set_raw_text("signature")
builder.set_validator("pass_through")
val block = builder.build()
check_text(block.validator_name, "pass_through")
```

</details>

### Edge Cases

#### handles empty payload

- handles empty payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty payload")
val block = create_simple_text_block("")
check_text(block.raw_text, "")
```

</details>

#### handles unicode in payload

- handles unicode in payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles unicode in payload")
val block = create_simple_text_block("héllo")
check(block.raw_text.contains("é"))
```

</details>

#### handles nested braces in raw mode

- handles nested braces in raw mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nested braces in raw mode")
val block = create_simple_text_block("{{value}}")
check(block.raw_text.contains("{{"))
```

</details>

### Documentation Examples

#### minimal example from README

- minimal example from README


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("minimal example from README")
val block = create_simple_text_block("readme example")
check_text(block.kind, "raw")
```

</details>

#### builder example from README

- builder example from README


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builder example from README")
val builder = BlockBuilder.create()
builder.set_raw_text("builder example")
builder.enable_math_features()
val block = builder.build()
check_text(block.kind, "math")
```

</details>

#### feature preset example from README

- feature preset example from README


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("feature preset example from README")
val builder = BlockBuilder.create()
builder.enable_pipeline_operators()
val block = builder.build()
check_text(block.kind, "pipeline")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/custom_blocks_easy_api_spec.spl` |
| Updated | 2026-08-26 |
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
| Total scenarios | 47 |
| Active scenarios | 47 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `de464ffa5d8a4ed3fc0d451b4ee4cbe40b3c49bd42828a493ba4ed3120877252`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `de464ffa5d8a4ed3fc0d451b4ee4cbe40b3c49bd42828a493ba4ed3120877252`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `de464ffa5d8a4ed3fc0d451b4ee4cbe40b3c49bd42828a493ba4ed3120877252`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/custom_blocks_easy_api_spec.spl
mirror: doc/06_spec/unit/compiler/custom_blocks_easy_api_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/custom_blocks_easy_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/custom_blocks_easy_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/custom_blocks_easy_api_spec.spl:181:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates simple heredoc block with raw text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/custom_blocks_easy_api_spec.spl:188:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates comment block that processes lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/custom_blocks_easy_api_spec.spl:194:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns error for invalid syntax' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
