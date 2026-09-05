# Preprocess Conditionals Specification

> Tests covering Preprocess Conditionals.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Preprocess Conditionals Specification

## Scenarios

### Preprocess Conditionals

#### should return directive-free source byte for byte without line rebuilding

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should return directive-free source byte for byte without line rebuilding
   - Expected: preprocess_conditionals(source) equals `source`
   - Expected: implementation contains `if not _pp_may_have_conditionals(source):`
   - Expected: implementation contains `return source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should return directive-free source byte for byte without line rebuilding")
val source = "# an ordinary @annotation-like comment\nfn main():\n    print(\"@cfg without paren\")\n"
expect(preprocess_conditionals(source)).to_equal(source)

val implementation = read_source("src/compiler/10.frontend/core/parser_preprocessor.spl")
expect(implementation.contains("if not _pp_may_have_conditionals(source):")).to_equal(true)
expect(implementation.contains("return source")).to_equal(true)
```

</details>

#### should expose conditional preprocessing through parser entrypoints

- should expose conditional preprocessing through parser entrypoints
   - Expected: parser_src contains `use compiler.frontend.core.parser_preprocessor`
   - Expected: parser_src contains `val preprocessed = _pp_preprocess_conditionals(source)`
   - Expected: parser_src contains `export _pp_preprocess_conditionals, preprocess_conditionals`
   - Expected: init_src contains `export preprocess_conditionals`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should expose conditional preprocessing through parser entrypoints")
val parser_src = read_source("src/compiler/10.frontend/core/parser.spl")
val init_src = read_source("src/compiler/10.frontend/core/__init__.spl")
expect(parser_src.contains("use compiler.frontend.core.parser_preprocessor")).to_equal(true)
expect(parser_src.contains("val preprocessed = _pp_preprocess_conditionals(source)")).to_equal(true)
expect(parser_src.contains("export _pp_preprocess_conditionals, preprocess_conditionals")).to_equal(true)
expect(init_src.contains("export preprocess_conditionals")).to_equal(true)
```

</details>

#### should recognize when elif else and end directives

- should recognize when elif else and end directives
   - Expected: src contains `fn _pp_preprocess_conditionals(source: text) -> text`
   - Expected: src contains `val is_when = trimmed.starts_with("@when(")`
   - Expected: src contains `val is_elif = trimmed.starts_with("@elif(")`
   - Expected: src contains `val is_else = trimmed == "@else" or trimmed == "@else:"`
   - Expected: src contains `val is_end = trimmed == "@end"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should recognize when elif else and end directives")
val src = read_source("src/compiler/10.frontend/core/parser_preprocessor.spl")
expect(src.contains("fn _pp_preprocess_conditionals(source: text) -> text")).to_equal(true)
expect(src.contains("val is_when = trimmed.starts_with(\"@when(\")")).to_equal(true)
expect(src.contains("val is_elif = trimmed.starts_with(\"@elif(\")")).to_equal(true)
expect(src.contains("val is_else = trimmed == \"@else\" or trimmed == \"@else:\"")).to_equal(true)
expect(src.contains("val is_end = trimmed == \"@end\"")).to_equal(true)
```

</details>

#### should preserve diagnostic line count for inactive branches

- should preserve diagnostic line count for inactive branches
   - Expected: src contains `if active:\n            out_lines.push(line)\n        else:`
   - Expected: src contains `out_lines.push("")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should preserve diagnostic line count for inactive branches")
val src = read_source("src/compiler/10.frontend/core/parser_preprocessor.spl")
# Anchored to the real active/inactive branch pair, not to the
# "# Keep line count stable for diagnostics." comment that used to be
# the only thing one of these needles could match.
expect(src.contains("if active:\n            out_lines.push(line)\n        else:")).to_equal(true)
expect(src.contains("out_lines.push(\"\")")).to_equal(true)
```

</details>

#### should honor target os and arch environment overrides

- should honor target os and arch environment overrides
   - Expected: src contains `cfg_env("SIMPLE_TARGET_OS")`
   - Expected: src contains `cfg_env("SIMPLE_TARGET_ARCH")`
   - Expected: src contains `fn cfg_detect_os() -> text`
   - Expected: src contains `fn cfg_detect_arch() -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should honor target os and arch environment overrides")
val src = read_source("src/compiler/10.frontend/core/cfg_platform.spl")
expect(src.contains("cfg_env(\"SIMPLE_TARGET_OS\")")).to_equal(true)
expect(src.contains("cfg_env(\"SIMPLE_TARGET_ARCH\")")).to_equal(true)
expect(src.contains("fn cfg_detect_os() -> text")).to_equal(true)
expect(src.contains("fn cfg_detect_arch() -> text")).to_equal(true)
```

</details>

#### should gate multi-line brace-delimited use imports under a false @cfg

- should gate multi-line brace-delimited use imports under a false @cfg
   - Expected: src contains `skip_until_close_brace`
   - Expected: src contains `next_trimmed.ends_with("{") and not next_trimmed.ends_with("}")`
   - Expected: src contains `brace_depth`
   - Expected: out does not contain `to_upper`
   - Expected: out does not contain `to_lower`
   - Expected: out contains `fn main():`
   - Expected: kept contains `to_upper`
   - Expected: kept contains `to_lower`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should gate multi-line brace-delimited use imports under a false @cfg")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Preprocess Conditionals.
- Preprocess Conditionals

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER_CORE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f31a09c4e51156aac15a06c43c851bb93e78126a33045f59310d7d75cd5cc8d7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f31a09c4e51156aac15a06c43c851bb93e78126a33045f59310d7d75cd5cc8d7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f31a09c4e51156aac15a06c43c851bb93e78126a33045f59310d7d75cd5cc8d7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler_core/preprocess_conditionals_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/preprocess_conditionals_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/preprocess_conditionals_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/preprocess_conditionals_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/preprocess_conditionals_spec.spl:16:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return directive-free source byte for byte without line rebuilding' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/preprocess_conditionals_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should return directive-free source byte for byte without line rebuilding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/preprocess_conditionals_spec.spl:26:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose conditional preprocessing through parser entrypoints' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/preprocess_conditionals_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose conditional preprocessing through parser entrypoints' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/preprocess_conditionals_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should recognize when elif else and end directives' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/preprocess_conditionals_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should recognize when elif else and end directives' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/preprocess_conditionals_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve diagnostic line count for inactive branches' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/preprocess_conditionals_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should honor target os and arch environment overrides' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/preprocess_conditionals_spec.spl:65:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should gate multi-line brace-delimited use imports under a false @cfg' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
