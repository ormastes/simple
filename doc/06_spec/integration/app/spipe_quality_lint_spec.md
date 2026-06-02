# Spipe Quality Lint Specification

## Scenarios

### spipe placeholder quality lint

#### flags tautological literal assertions

1. count_lint(source, "SPIPE001") equals `1`
   - Expected: count_lint(source, "SPIPE001") equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"uses fake success\":\n" +
    "        expect(true).to_equal(true)\n"

expect(count_lint(source, "SPIPE001")).to_equal(1)
```

</details>

#### flags placeholder pass helpers inside examples

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"uses pass helper\":\n" +
    "        pass_todo\n"

expect(count_lint(source, "SPIPE002")).to_equal(1)
```

</details>

#### flags placeholder pass helpers with rationale arguments inside examples

1. "        pass todo
   - Expected: count_lint(source, "SPIPE002") equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"uses pass helper call\":\n" +
    "        pass_todo(\"blocked until driver smoke exists\")\n"

expect(count_lint(source, "SPIPE002")).to_equal(1)
```

</details>

#### flags placeholder match-arm success assertions

1. "        match run check

2. "            case Ok

3. "            case Err
   - Expected: count_lint(source, "SPIPE003") equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"uses fake ok arm\":\n" +
    "        match run_check():\n" +
    "            case Ok(_): expect(true).to_equal(true)\n" +
    "            case Err(e): expect(e).to_equal(\"boom\")\n"

expect(count_lint(source, "SPIPE003")).to_equal(1)
```

</details>

#### flags print based skip placeholders

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"prints skip and returns\":\n" +
    "        print \"[skip] env unavailable\"\n" +
    "        return\n"

expect(count_lint(source, "SPIPE004")).to_equal(1)
```

</details>

#### flags examples with no real assertion

1. "        run check
   - Expected: count_lint(source, "SPIPE005") equals `1`


<details>
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"empty\":\n"

expect(count_lint(source, "SPIPE005")).to_equal(1)
```

</details>

#### flags boolean-wrapper assertions

1. count_lint(source, "SPIPE006") equals `1`
   - Expected: count_lint(source, "SPIPE006") equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"wraps comparison\":\n" +
    "        expect(code != 0).to_equal(true)\n"

expect(count_lint(source, "SPIPE006")).to_equal(1)
```

</details>

#### flags false boolean-wrapper assertions

1. count_lint(source, "SPIPE006") equals `1`
   - Expected: count_lint(source, "SPIPE006") equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "describe \"demo\":\n" +
    "    it \"wraps negative boolean\":\n" +
    "        val ok = false\n" +
    "        expect(ok).to_equal(false)\n"

expect(count_lint(source, "SPIPE006")).to_equal(1)
```

</details>

#### flags to_be boolean wrappers

1. count_lint(true_source, "SPIPE006") equals `1`
2. count_lint(false_source, "SPIPE006") equals `1`
   - Expected: count_lint(true_source, "SPIPE006") equals `1`
   - Expected: count_lint(false_source, "SPIPE006") equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val true_source =
    "describe \"demo\":\n" +
    "    it \"wraps true with to_be\":\n" +
    "        expect(code != 0).to_be(true)\n"
val false_source =
    "describe \"demo\":\n" +
    "    it \"wraps false with to_be\":\n" +
    "        expect(ok).to_be(false)\n"

expect(count_lint(true_source, "SPIPE006")).to_equal(1)
expect(count_lint(false_source, "SPIPE006")).to_equal(1)
```

</details>

#### allows concise boolean assertions

1. source includes concise `expect(ok)`
2. source includes concise `expect_not(failed)`
   - Expected: total_spipe_quality_lints(source) equals `0`


<details>
<summary>Executable SPipe</summary>

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

2. "    pass todo
   - Expected: count_lint_for_path("src/os/demo.spl", source, "STUB003") equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "fn not_done(port: i64) -> i64:\n" +
    "    pass_todo(\"implement driver\")\n"

expect(count_lint_for_path("src/os/demo.spl", source, "STUB003")).to_equal(1)
```

</details>

#### flags bare pass_todo in production code

1. "fn not done
   - Expected: count_lint_for_path("src/os/demo.spl", source, "STUB003") equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "fn not_done(port: i64) -> i64:\n" +
    "    pass_todo\n"

expect(count_lint_for_path("src/os/demo.spl", source, "STUB003")).to_equal(1)
```

</details>

#### allows sanctioned skip syntax

<details>
<summary>Executable SPipe</summary>

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

1. source includes `@allow(spipe_placeholder_tests)`
2. source includes placeholder assertion under the allow annotation
   - Expected: total_spipe_quality_lints(source) equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "@" + "allow(spipe_placeholder_tests)\n" +
    "describe \"demo\":\n" +
    "    it \"permits migration file\":\n" +
    "        expect(true).to_equal(true)\n"

expect(total_spipe_quality_lints(source)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/spipe_quality_lint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- spipe placeholder quality lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
