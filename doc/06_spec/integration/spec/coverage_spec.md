# Coverage Specification

> Tests covering Coverage System Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coverage Specification

## Scenarios

### Coverage System Integration

#### CoverageCalculator - Function Level

#### tracks function coverage

- tracks function coverage


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tracks function coverage")
val calculator = function_coverage()

calculator.add_function("add", "math", "public")
calculator.add_function("subtract", "math", "public")
calculator.add_function("multiply", "math", "public")

# Mark some functions as touched
calculator.mark_function_touched("add", "math", "test_addition")
calculator.mark_function_touched("subtract", "math", "test_subtraction")

val stats = calculator.calculate_stats()

expect(stats.total_count).to eq(3)
expect(stats.touched_count).to eq(2)
expect(stats.untouched_count).to eq(1)
expect(stats.coverage_percentage).to gt(66.0)
expect(stats.coverage_percentage).to lt(67.0)
```

</details>

#### tracks multiple touches of same function

- tracks multiple touches of same function


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tracks multiple touches of same function")
val calculator = function_coverage()

calculator.add_function("add", "math", "public")
calculator.mark_function_touched("add", "math", "test1")
calculator.mark_function_touched("add", "math", "test2")
calculator.mark_function_touched("add", "math", "test3")

val touched = calculator.get_touched()
expect(touched.len()).to eq(1)
expect(touched[0].touch_count).to eq(3)
expect(touched[0].touched_by.len()).to eq(3)
```

</details>

#### filters by public visibility

- filters by public visibility


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("filters by public visibility")
val calculator = function_coverage()

calculator.add_function("public_fn", "mod", "public")
calculator.add_function("private_fn", "mod", "private")

calculator.mark_function_touched("public_fn", "mod", "test")
calculator.mark_function_touched("private_fn", "mod", "test")

val stats = calculator.calculate_stats()

# Only public function counted
expect(stats.total_count).to eq(1)
expect(stats.touched_count).to eq(1)
```

</details>

#### can include private functions

- can include private functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("can include private functions")
val calculator = function_coverage().include_private()

calculator.add_function("public_fn", "mod", "public")
calculator.add_function("private_fn", "mod", "private")

calculator.mark_function_touched("public_fn", "mod", "test")

val stats = calculator.calculate_stats()

# Both functions counted
expect(stats.total_count).to eq(2)
expect(stats.touched_count).to eq(1)
```

</details>

#### CoverageCalculator - Method Level

#### tracks method coverage

- tracks method coverage


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tracks method coverage")
val calculator = method_coverage()

calculator.add_method("add", "Calculator", "math", "public")
calculator.add_method("subtract", "Calculator", "math", "public")
calculator.add_method("new", "Calculator", "math", "public")

calculator.mark_method_touched("add", "Calculator", "math", "test_add")
calculator.mark_method_touched("new", "Calculator", "math", "test_add")

val stats = calculator.calculate_stats()

expect(stats.total_count).to eq(3)
expect(stats.touched_count).to eq(2)
```

</details>

#### distinguishes methods with same name in different structs

- distinguishes methods with same name in different structs


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("distinguishes methods with same name in different structs")
val calculator = method_coverage()

calculator.add_method("new", "Calculator", "math", "public")
calculator.add_method("new", "Parser", "parse", "public")

calculator.mark_method_touched("new", "Calculator", "math", "test")

val stats = calculator.calculate_stats()

expect(stats.touched_count).to eq(1)
expect(stats.untouched_count).to eq(1)
```

</details>

#### CoverageCalculator - Line Level

#### tracks line coverage

- tracks line coverage


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tracks line coverage")
val calculator = line_coverage()

calculator.add_line("file.spl", 10)
calculator.add_line("file.spl", 15)
calculator.add_line("file.spl", 20)

calculator.mark_line_touched("file.spl", 10, "test1")
calculator.mark_line_touched("file.spl", 15, "test1")

val stats = calculator.calculate_stats()

expect(stats.total_count).to eq(3)
expect(stats.touched_count).to eq(2)
```

</details>

#### CoverageStats

#### calculates coverage percentage correctly

- calculates coverage percentage correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("calculates coverage percentage correctly")
val stats = CoverageStats.new(10, 7)

expect(stats.total_count).to eq(10)
expect(stats.touched_count).to eq(7)
expect(stats.untouched_count).to eq(3)
expect(stats.coverage_percentage).to eq(70.0)
```

</details>

#### handles 100% coverage

- handles 100% coverage


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles 100% coverage")
val stats = CoverageStats.new(5, 5)

expect(stats.is_complete()).to be_true()
expect(stats.coverage_percentage).to eq(100.0)
```

</details>

#### handles 0% coverage

- handles 0% coverage


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles 0% coverage")
val stats = CoverageStats.new(5, 0)

expect(stats.is_complete()).to be_false()
expect(stats.coverage_percentage).to eq(0.0)
```

</details>

#### handles empty target list

- handles empty target list


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles empty target list")
val stats = CoverageStats.new(0, 0)

expect(stats.coverage_percentage).to eq(100.0)
expect(stats.is_complete()).to be_true()
```

</details>

#### checks threshold acceptance

- checks threshold acceptance


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("checks threshold acceptance")
val stats = CoverageStats.new(10, 8)

expect(stats.is_acceptable(80.0)).to be_true()
expect(stats.is_acceptable(85.0)).to be_false()
```

</details>

#### generates summary string

- generates summary string


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates summary string")
val stats = CoverageStats.new(10, 7)

val summary = stats.summary()
expect(summary).to include_string("7/10")
expect(summary).to include_string("70.00%")
```

</details>

#### Per-Module Coverage

#### calculates module-specific coverage

- calculates module-specific coverage


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("calculates module-specific coverage")
val calculator = function_coverage()

calculator.add_function("add", "math", "public")
calculator.add_function("parse", "parser", "public")
calculator.add_function("format", "formatter", "public")

calculator.mark_function_touched("add", "math", "test")
calculator.mark_function_touched("format", "formatter", "test")

val math_stats = calculator.calculate_module_stats("math")
expect(math_stats.total_count).to eq(1)
expect(math_stats.touched_count).to eq(1)

val parser_stats = calculator.calculate_module_stats("parser")
expect(parser_stats.total_count).to eq(1)
expect(parser_stats.touched_count).to eq(0)
```

</details>

#### lists all modules

- lists all modules


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("lists all modules")
val calculator = function_coverage()

calculator.add_function("f1", "mod1", "public")
calculator.add_function("f2", "mod2", "public")
calculator.add_function("f3", "mod1", "public")

val modules = calculator.get_modules()
expect(modules.len()).to eq(2)
expect(modules.contains("mod1")).to be_true()
expect(modules.contains("mod2")).to be_true()
```

</details>

#### gets entries by module

- gets entries by module


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gets entries by module")
val calculator = function_coverage()

calculator.add_function("f1", "mod1", "public")
calculator.add_function("f2", "mod2", "public")
calculator.add_function("f3", "mod1", "public")

val mod1_entries = calculator.get_by_module("mod1")
expect(mod1_entries.len()).to eq(2)

val mod2_entries = calculator.get_by_module("mod2")
expect(mod2_entries.len()).to eq(1)
```

</details>

#### Coverage Queries

#### gets untouched targets

- gets untouched targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gets untouched targets")
val calculator = function_coverage()

calculator.add_function("f1", "mod", "public")
calculator.add_function("f2", "mod", "public")
calculator.add_function("f3", "mod", "public")

calculator.mark_function_touched("f1", "mod", "test")

val untouched = calculator.get_untouched()
expect(untouched.len()).to eq(2)
```

</details>

#### gets touched targets

- gets touched targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gets touched targets")
val calculator = function_coverage()

calculator.add_function("f1", "mod", "public")
calculator.add_function("f2", "mod", "public")

calculator.mark_function_touched("f1", "mod", "test")

val touched = calculator.get_touched()
expect(touched.len()).to eq(1)
expect(touched[0].touched).to be_true()
```

</details>

#### TerminalReporter

#### generates coverage summary

- generates coverage summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates coverage summary")
val calculator = function_coverage()

calculator.add_function("f1", "mod", "public")
calculator.add_function("f2", "mod", "public")
calculator.add_function("f3", "mod", "public")

calculator.mark_function_touched("f1", "mod", "test")
calculator.mark_function_touched("f2", "mod", "test")

val reporter = TerminalReporter.new().without_colors()

# Just verify it doesn't crash
# In real usage, would capture output
reporter.print_report(calculator)
```

</details>

#### can disable colors

- can disable colors


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("can disable colors")
val reporter = TerminalReporter.new().without_colors()
expect(reporter.show_colors).to be_false()
```

</details>

#### can show/hide sections

- can show/hide sections


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("can show/hide sections")
val reporter = TerminalReporter.new()
    .without_untouched()
    .with_touched()
    .without_per_module()

expect(reporter.show_untouched).to be_false()
expect(reporter.show_touched).to be_true()
expect(reporter.show_per_module).to be_false()
```

</details>

#### can set threshold

- can set threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("can set threshold")
val reporter = TerminalReporter.new().with_threshold(90.0)
expect(reporter.threshold).to eq(90.0)
```

</details>

#### CompactReporter

#### generates compact summary

- generates compact summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates compact summary")
val calculator = function_coverage()

calculator.add_function("f1", "mod", "public")
calculator.add_function("f2", "mod", "public")

calculator.mark_function_touched("f1", "mod", "test")

val reporter = CompactReporter.new().without_colors()

# Verify it doesn't crash
reporter.print_report(calculator)
```

</details>

#### HtmlReporter

#### generates HTML report

- generates HTML report


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates HTML report")
val calculator = function_coverage()

calculator.add_function("add", "math", "public")
calculator.add_function("subtract", "math", "public")

calculator.mark_function_touched("add", "math", "test")

val reporter = HtmlReporter.new()
val html = reporter.generate_html(calculator)

expect(html).to include_string("<!DOCTYPE html>")
expect(html).to include_string("Coverage Summary")
expect(html).to include_string("50.00%")
expect(html).to include_string("math")
```

</details>

#### can set custom title

- can set custom title


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("can set custom title")
val reporter = HtmlReporter.new().with_title("My Coverage Report")
expect(reporter.title).to eq("My Coverage Report")
```

</details>

#### can include source

- can include source


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("can include source")
val reporter = HtmlReporter.new().with_source()
expect(reporter.include_source).to be_true()
```

</details>

#### JsonCoverageReporter

#### generates JSON coverage report

- generates JSON coverage report


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates JSON coverage report")
val calculator = function_coverage()

calculator.add_function("add", "math", "public")
calculator.add_function("subtract", "math", "public")

calculator.mark_function_touched("add", "math", "test")

val reporter = JsonCoverageReporter.new()
val json_str = reporter.to_json(calculator)

expect(json_str).to include_string("summary")
expect(json_str).to include_string("modules")
expect(json_str).to include_string("metadata")
expect(json_str).to include_string("50")  # 50% coverage
```

</details>

#### can pretty-print JSON

- can pretty-print JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("can pretty-print JSON")
val calculator = function_coverage()
calculator.add_function("f1", "mod", "public")

val reporter = JsonCoverageReporter.new().with_pretty_print()
val json_str = reporter.to_json(calculator)

expect(json_str).to include_string("\n")  # Newlines indicate pretty print
```

</details>

#### can exclude targets

- can exclude targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("can exclude targets")
val reporter = JsonCoverageReporter.new().without_targets()
expect(reporter.include_targets).to be_false()
```

</details>

#### can include touched_by info

- can include touched_by info


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("can include touched_by info")
val reporter = JsonCoverageReporter.new().with_touched_by()
expect(reporter.include_touched_by).to be_true()
```

</details>

#### CodecovReporter

#### generates Codecov-compatible JSON

- generates Codecov-compatible JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates Codecov-compatible JSON")
val calculator = function_coverage()

calculator.add_function("f1", "module1", "public")
calculator.add_function("f2", "module1", "public")

calculator.mark_function_touched("f1", "module1", "test")

val reporter = CodecovReporter.new()
val json_str = reporter.to_json(calculator)

expect(json_str).to include_string("coverage")
expect(json_str).to include_string("files")
```

</details>

#### CoverallsReporter

#### generates Coveralls-compatible JSON

- generates Coveralls-compatible JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates Coveralls-compatible JSON")
val calculator = function_coverage()

calculator.add_function("f1", "module1", "public")
calculator.add_function("f2", "module1", "public")

calculator.mark_function_touched("f1", "module1", "test")

val reporter = CoverallsReporter.new()
val json_str = reporter.to_json(calculator)

expect(json_str).to include_string("service_name")
expect(json_str).to include_string("source_files")
```

</details>

#### End-to-End Coverage Workflow

#### tracks coverage from test execution

- tracks coverage from test execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tracks coverage from test execution")
# Simulate a test suite
val calculator = function_coverage()

# Register functions from a hypothetical module
calculator.add_function("add", "calculator", "public")
calculator.add_function("subtract", "calculator", "public")
calculator.add_function("multiply", "calculator", "public")
calculator.add_function("divide", "calculator", "public")

# Simulate test execution touching functions
calculator.mark_function_touched("add", "calculator", "test_addition")
calculator.mark_function_touched("subtract", "calculator", "test_subtraction")
calculator.mark_function_touched("multiply", "calculator", "test_multiplication")

# Calculate coverage
val stats = calculator.calculate_stats()

expect(stats.total_count).to eq(4)
expect(stats.touched_count).to eq(3)
expect(stats.coverage_percentage).to eq(75.0)

# Verify we can identify untouched
val untouched = calculator.get_untouched()
expect(untouched.len()).to eq(1)

# Generate reports (verify they don't crash)
val terminal = TerminalReporter.new().without_colors()
terminal.print_report(calculator)

val html = HtmlReporter.new().generate_html(calculator)
expect(html).to include_string("75.00%")

val json = JsonCoverageReporter.new().to_json(calculator)
expect(json).to include_string("\"coverage_percentage\":75")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/spec/coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Coverage System Integration.
- Coverage System Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1f57bbda60e1c9c450a5ac5f59dd1f855caa77ab2fa3988122ba889429d3a22f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1f57bbda60e1c9c450a5ac5f59dd1f855caa77ab2fa3988122ba889429d3a22f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1f57bbda60e1c9c450a5ac5f59dd1f855caa77ab2fa3988122ba889429d3a22f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/spec/coverage_spec.spl
mirror: doc/06_spec/integration/spec/coverage_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/spec/coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/spec/coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/spec/coverage_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks function coverage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/spec/coverage_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks multiple touches of same function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/spec/coverage_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters by public visibility' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/spec/coverage_spec.spl:73:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can include private functions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/integration/spec/coverage_spec.spl:290:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can disable colors' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/integration/spec/coverage_spec.spl:296:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can show/hide sections' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/integration/spec/coverage_spec.spl:308:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can set threshold' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/integration/spec/coverage_spec.spl:349:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can set custom title' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/integration/spec/coverage_spec.spl:355:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can include source' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
