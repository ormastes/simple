# Preprocess Conditionals Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Preprocess Conditionals Specification

## Scenarios

### Preprocess Conditionals

#### should return directive-free source byte for byte without line rebuilding

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "# an ordinary @annotation-like comment\nfn main():\n    print(\"@cfg without paren\")\n"
expect(preprocess_conditionals(source)).to_equal(source)

val implementation = read_source("src/compiler/10.frontend/core/parser_preprocessor.spl")
expect(implementation).to_contain("if not _pp_may_have_conditionals(source):")
expect(implementation).to_contain("return source")
```

</details>

#### should preserve directive-looking triple-quoted text and still blank inactive branches

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val guide = \"\"\"\n@when(false)\nkept when text\n@end\n@cfg(false)\nkept cfg text\n\"\"\"\n@when(false)\nval hidden = 1\n@end\nval visible = 2\n"
val out = preprocess_conditionals(source)

expect(out).to_contain("@when(false)\nkept when text\n@end")
expect(out).to_contain("@cfg(false)\nkept cfg text")
expect(out.contains("val hidden = 1")).to_be(false)
expect(out).to_contain("val visible = 2")
```

</details>

#### should expose conditional preprocessing through parser entrypoints

<details>
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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

#### should gate multi-line brace-delimited use imports under a false @cfg

- "@cfg
   - Expected: out does not contain `to_upper`
   - Expected: out does not contain `to_lower`
   - Expected: out contains `fn main():`
- "@cfg
   - Expected: kept contains `to_upper`
   - Expected: kept contains `to_lower`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Regression for the hal.spl import-closure bug: @cfg only blanked a
# single following line, so a multi-line `use module.{ ... }` import
# (opening brace on the @cfg'd line, closing brace on a later line)
# left its continuation lines as dangling unconditional source when
# the condition was false. Fixed by tracking brace depth through the
# matching close, symmetric with the existing colon/dedent handling.
val src = read_source("src/compiler/10.frontend/core/parser_preprocessor.spl")
expect(src.contains("skip_until_close_brace")).to_equal(true)
expect(src.contains("next_trimmed.ends_with(\"{\") and not next_trimmed.ends_with(\"}\")")).to_equal(true)
expect(src.contains("brace_depth")).to_equal(true)

val out = preprocess_conditionals(
    "@cfg(arm64)\nuse std.text.{\n    to_upper,\n    to_lower\n}\n\nfn main():\n    print(1)\n"
)
expect(out.contains("to_upper")).to_equal(false)
expect(out.contains("to_lower")).to_equal(false)
expect(out.contains("fn main():")).to_equal(true)

val kept = preprocess_conditionals(
    "@cfg(x86_64)\nuse std.text.{\n    to_upper,\n    to_lower\n}\n\nfn main():\n    print(1)\n"
)
expect(kept.contains("to_upper")).to_equal(true)
expect(kept.contains("to_lower")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/preprocess_conditionals_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Preprocess Conditionals

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
