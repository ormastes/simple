# Coverage Specification

> 1. calculator add function

<!-- sdn-diagram:id=coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

coverage_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1. calculator add function
2. calculator add function
3. calculator add function
4. calculator mark function touched
5. calculator mark function touched


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. calculator add function
2. calculator mark function touched
3. calculator mark function touched
4. calculator mark function touched


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. calculator add function
2. calculator add function
3. calculator mark function touched
4. calculator mark function touched


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. calculator add function
2. calculator add function
3. calculator mark function touched


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. calculator add method
2. calculator add method
3. calculator add method
4. calculator mark method touched
5. calculator mark method touched


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. calculator add method
2. calculator add method
3. calculator mark method touched


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. calculator add line
2. calculator add line
3. calculator add line
4. calculator mark line touched
5. calculator mark line touched


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = CoverageStats.new(10, 7)

expect(stats.total_count).to eq(10)
expect(stats.touched_count).to eq(7)
expect(stats.untouched_count).to eq(3)
expect(stats.coverage_percentage).to eq(70.0)
```

</details>

#### handles 100% coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = CoverageStats.new(5, 5)

expect(stats.is_complete()).to be_true()
expect(stats.coverage_percentage).to eq(100.0)
```

</details>

#### handles 0% coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = CoverageStats.new(5, 0)

expect(stats.is_complete()).to be_false()
expect(stats.coverage_percentage).to eq(0.0)
```

</details>

#### handles empty target list

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = CoverageStats.new(0, 0)

expect(stats.coverage_percentage).to eq(100.0)
expect(stats.is_complete()).to be_true()
```

</details>

#### checks threshold acceptance

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = CoverageStats.new(10, 8)

expect(stats.is_acceptable(80.0)).to be_true()
expect(stats.is_acceptable(85.0)).to be_false()
```

</details>

#### generates summary string

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = CoverageStats.new(10, 7)

val summary = stats.summary()
expect(summary).to include_string("7/10")
expect(summary).to include_string("70.00%")
```

</details>

#### Per-Module Coverage

#### calculates module-specific coverage

1. calculator add function
2. calculator add function
3. calculator add function
4. calculator mark function touched
5. calculator mark function touched


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. calculator add function
2. calculator add function
3. calculator add function


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. calculator add function
2. calculator add function
3. calculator add function


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. calculator add function
2. calculator add function
3. calculator add function
4. calculator mark function touched


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. calculator add function
2. calculator add function
3. calculator mark function touched


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. calculator add function
2. calculator add function
3. calculator add function
4. calculator mark function touched
5. calculator mark function touched
6. reporter print report


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reporter = TerminalReporter.new().without_colors()
expect(reporter.show_colors).to be_false()
```

</details>

#### can show/hide sections

1.  without untouched
2.  with touched
3.  without per module


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reporter = TerminalReporter.new().with_threshold(90.0)
expect(reporter.threshold).to eq(90.0)
```

</details>

#### CompactReporter

#### generates compact summary

1. calculator add function
2. calculator add function
3. calculator mark function touched
4. reporter print report


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. calculator add function
2. calculator add function
3. calculator mark function touched


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reporter = HtmlReporter.new().with_title("My Coverage Report")
expect(reporter.title).to eq("My Coverage Report")
```

</details>

#### can include source

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reporter = HtmlReporter.new().with_source()
expect(reporter.include_source).to be_true()
```

</details>

#### JsonCoverageReporter

#### generates JSON coverage report

1. calculator add function
2. calculator add function
3. calculator mark function touched


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. calculator add function


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calculator = function_coverage()
calculator.add_function("f1", "mod", "public")

val reporter = JsonCoverageReporter.new().with_pretty_print()
val json_str = reporter.to_json(calculator)

expect(json_str).to include_string("\n")  # Newlines indicate pretty print
```

</details>

#### can exclude targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reporter = JsonCoverageReporter.new().without_targets()
expect(reporter.include_targets).to be_false()
```

</details>

#### can include touched_by info

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reporter = JsonCoverageReporter.new().with_touched_by()
expect(reporter.include_touched_by).to be_true()
```

</details>

#### CodecovReporter

#### generates Codecov-compatible JSON

1. calculator add function
2. calculator add function
3. calculator mark function touched


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. calculator add function
2. calculator add function
3. calculator mark function touched


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. calculator add function
2. calculator add function
3. calculator add function
4. calculator add function
5. calculator mark function touched
6. calculator mark function touched
7. calculator mark function touched
8. terminal print report


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/02_integration/spec/coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
