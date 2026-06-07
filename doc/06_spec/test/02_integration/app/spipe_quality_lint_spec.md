# Spipe Quality Lint Specification

> <details>

<!-- sdn-diagram:id=spipe_quality_lint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spipe_quality_lint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spipe_quality_lint_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spipe_quality_lint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spipe Quality Lint Specification

## Scenarios

### spipe placeholder quality lint

#### flags tautological literal assertions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"uses fake success\":\n" +
    "        expect(true).to_equal(" + "true)\n"

expect(count_lint(source, "SPIPE001")).to_equal(1)
```

</details>

#### flags placeholder pass helpers inside examples

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"uses pass helper\":\n" +
    "        pass_" + "todo\n"

expect(count_lint(source, "SPIPE002")).to_equal(1)
```

</details>

#### flags placeholder pass helpers with rationale arguments inside examples

1. "        pass " + "todo
   - Expected: count_lint(source, "SPIPE002") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"uses pass helper call\":\n" +
    "        pass_" + "todo(\"blocked until driver smoke exists\")\n"

expect(count_lint(source, "SPIPE002")).to_equal(1)
```

</details>

#### flags placeholder match-arm success assertions

1. "        match run check
   - Expected: count_lint(source, "SPIPE003") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"uses fake ok arm\":\n" +
    "        match run_check():\n" +
    "            case Ok(_): expect(true).to_equal(" + "true)\n" +
    "            case Err(e): expect(e).to_equal(\"boom\")\n"

expect(count_lint(source, "SPIPE003")).to_equal(1)
```

</details>

#### flags print based skip placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"prints skip and returns\":\n" +
    "        print \"" + "[skip] env unavailable\"\n" +
    "        return\n"

expect(count_lint(source, "SPIPE004")).to_equal(1)
```

</details>

#### flags examples with no real assertion

1. "        run check
   - Expected: count_lint(source, "SPIPE005") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"just calls helper\":\n" +
    "        run_check()\n"

expect(count_lint(source, "SPIPE005")).to_equal(1)
```

</details>

#### flags examples with empty bodies

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"empty\":\n"

expect(count_lint(source, "SPIPE005")).to_equal(1)
```

</details>

#### warns for true boolean-wrapper assertions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"wraps comparison\":\n" +
    "        expect(code != 0).to_equal(" + "true)\n"

expect(count_lint(source, "SPIPE006")).to_equal(1)
expect(count_lint_with_level(source, "SPIPE006", LintLevel.Warn)).to_equal(1)
```

</details>

#### warns for false boolean-wrapper assertions

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"wraps negative boolean\":\n" +
    "        val ok = false\n" +
    "        expect(ok).to_equal(" + "false)\n"

expect(count_lint(source, "SPIPE007")).to_equal(1)
expect(count_lint_with_level(source, "SPIPE007", LintLevel.Warn)).to_equal(1)
```

</details>

#### flags to_be boolean wrappers

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val true_source =
    "describe \"demo\":\n" +
    "    it \"wraps true with to_be\":\n" +
    "        expect(code != 0).to_be(" + "true)\n"
val false_source =
    "describe \"demo\":\n" +
    "    it \"wraps false with to_be\":\n" +
    "        expect(ok).to_be(" + "false)\n"

expect(count_lint(true_source, "SPIPE006")).to_equal(1)
expect(count_lint(false_source, "SPIPE007")).to_equal(1)
```

</details>

#### warns for is_equal boolean wrappers

1. "        expect
2. "        expect
   - Expected: count_lint(true_source, "SPIPE006") equals `1`
   - Expected: count_lint_with_level(true_source, "SPIPE006", LintLevel.Warn) equals `1`
   - Expected: count_lint_message_containing(true_source, "SPIPE006", "expect(bool) is called with a boolean matcher") equals `1`
   - Expected: count_lint_message_containing(true_source, "SPIPE006", "use expect(condition)") equals `1`
   - Expected: count_lint(false_source, "SPIPE007") equals `1`
   - Expected: count_lint_with_level(false_source, "SPIPE007", LintLevel.Warn) equals `1`
   - Expected: count_lint_message_containing(false_source, "SPIPE007", "expect(bool) is called with a boolean matcher") equals `1`
   - Expected: count_lint_message_containing(false_source, "SPIPE007", "use expect_not(condition)") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val true_source =
    "describe \"demo\":\n" +
    "    it \"wraps true with is_equal\":\n" +
    "        expect(code != 0).is_equal(" + "true)\n"
val false_source =
    "describe \"demo\":\n" +
    "    it \"wraps false with is_equal\":\n" +
    "        expect(ok).is_equal(" + "false)\n"

expect(count_lint(true_source, "SPIPE006")).to_equal(1)
expect(count_lint_with_level(true_source, "SPIPE006", LintLevel.Warn)).to_equal(1)
expect(count_lint_message_containing(true_source, "SPIPE006", "expect(bool) is called with a boolean matcher")).to_equal(1)
expect(count_lint_message_containing(true_source, "SPIPE006", "use expect(condition)")).to_equal(1)
expect(count_lint(false_source, "SPIPE007")).to_equal(1)
expect(count_lint_with_level(false_source, "SPIPE007", LintLevel.Warn)).to_equal(1)
expect(count_lint_message_containing(false_source, "SPIPE007", "expect(bool) is called with a boolean matcher")).to_equal(1)
expect(count_lint_message_containing(false_source, "SPIPE007", "use expect_not(condition)")).to_equal(1)
```

</details>

#### allows concise boolean assertions

1. "        expect
2. "        expect not
   - Expected: total_spipe_quality_lints(source) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"uses concise boolean expectations\":\n" +
    "        val ok = true\n" +
    "        val failed = false\n" +
    "        expect(ok)\n" +
    "        expect_not(failed)\n"

expect(total_spipe_quality_lints(source)).to_equal(0)
```

</details>

#### flags pass_todo in production code

1. "fn not done
2. "    pass " + "todo
   - Expected: count_lint_for_path("src/os/demo.spl", source, "STUB003") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "fn not_done(port: i64) -> i64:\n" +
    "    pass_" + "todo(\"implement driver\")\n"

expect(count_lint_for_path("src/os/demo.spl", source, "STUB003")).to_equal(1)
```

</details>

#### flags bare pass_todo in production code

1. "fn not done
   - Expected: count_lint_for_path("src/os/demo.spl", source, "STUB003") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "fn not_done(port: i64) -> i64:\n" +
    "    pass_" + "todo\n"

expect(count_lint_for_path("src/os/demo.spl", source, "STUB003")).to_equal(1)
```

</details>

#### allows sanctioned skip syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"skips honestly\":\n" +
    "        skip:\n"

expect(total_spipe_quality_lints(source)).to_equal(0)
```

</details>

#### respects allow on spipe_placeholder_tests

1. "@" + "allow
   - Expected: total_spipe_quality_lints(source) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "@" + "allow(spipe_placeholder_tests)\n" +
    "describe \"demo\":\n" +
    "    it \"permits migration file\":\n" +
    "        expect(true).to_equal(" + "true)\n"

expect(total_spipe_quality_lints(source)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/spipe_quality_lint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- spipe placeholder quality lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
