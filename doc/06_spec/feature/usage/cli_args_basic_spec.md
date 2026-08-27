# CLI Args Basic Specification

> Exercises the `cli` keyword's argument parsing behavior (bool flags, string options, int options, default values) through the real parser (std.nogc_sync_mut.cli.cli_parser) instead of commented-out pseudo-code.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args Basic Specification

Exercises the `cli` keyword's argument parsing behavior (bool flags, string options, int options, default values) through the real parser (std.nogc_sync_mut.cli.cli_parser) instead of commented-out pseudo-code.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-001 |
| Category | Language \| CLI |
| Status | Implemented |
| Source | `test/feature/usage/cli_args_basic_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exercises the `cli` keyword's argument parsing behavior (bool flags, string
options, int options, default values) through the real parser
(std.nogc_sync_mut.cli.cli_parser) instead of commented-out pseudo-code.

## Syntax

```simple
cli:
    verbose: false        # --verbose / -v bool flag
    output: "out.txt"     # --output / -o string option
    count: 1              # --count / -c int option
```

## Scenarios

### CLI Args Basic

#### bool flags

#### bool flag defaults to false and --verbose/-v set it true

- Verify: flag default false, long and short forms set true
   - Expected: parsed_flag(parse_cli_args(spec, []), "verbose") is false
   - Expected: parsed_flag(parse_cli_args(spec, ["--verbose"]), "verbose") is true
   - Expected: parsed_flag(parse_cli_args(spec, ["-v"]), "verbose") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: flag default false, long and short forms set true")
val spec = cli_spec_flag(cli_spec(), "verbose", "v", "verbose output")
expect(parsed_flag(parse_cli_args(spec, []), "verbose")).to_equal(false)  # oracle: unset flag is false
expect(parsed_flag(parse_cli_args(spec, ["--verbose"]), "verbose")).to_equal(true)  # oracle: long form sets flag
expect(parsed_flag(parse_cli_args(spec, ["-v"]), "verbose")).to_equal(true)  # oracle: short form sets flag
```

</details>

#### string options

#### string option keeps its default and accepts --key=value and --key value

- Verify: option default, = form, and space form
   - Expected: parsed_option(parse_cli_args(spec, []), "output") equals `out.txt`
   - Expected: parsed_option(parse_cli_args(spec, ["--output=a.txt"]), "output") equals `a.txt`
   - Expected: parsed_option(parse_cli_args(spec, ["--output", "b.txt"]), "output") equals `b.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: option default, = form, and space form")
val spec = cli_spec_option(cli_spec(), "output", "o", "output path", "out.txt", [])
expect(parsed_option(parse_cli_args(spec, []), "output")).to_equal("out.txt")  # oracle: default retained
expect(parsed_option(parse_cli_args(spec, ["--output=a.txt"]), "output")).to_equal("a.txt")  # oracle: = form parsed
expect(parsed_option(parse_cli_args(spec, ["--output", "b.txt"]), "output")).to_equal("b.txt")  # oracle: space form parsed
```

</details>

#### unrelated string option is unaffected by flag parsing

- Verify: parsing a flag leaves a sibling option at its default
   - Expected: parsed_option(parse_cli_args(spec, ["-q"]), "mode") equals `release`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: parsing a flag leaves a sibling option at its default")
val spec = cli_spec_option(cli_spec(), "mode", "m", "run mode", "release", [])
expect(parsed_option(parse_cli_args(spec, ["-q"]), "mode")).to_equal("release")  # oracle: unknown flag does not clobber options
```

</details>

#### int options

#### int option parses as a numeric string with default

- Verify: count option default 1 and parsed value round-trips to int
   - Expected: parsed_option(parse_cli_args(spec, []), "count").to_i64() equals `1`
   - Expected: parsed_option(parse_cli_args(spec, ["--count=3"]), "count").to_i64() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: count option default 1 and parsed value round-trips to int")
val spec = cli_spec_option(cli_spec(), "count", "c", "repeat count", "1", [])
expect(parsed_option(parse_cli_args(spec, []), "count").to_i64()).to_equal(1)  # oracle: default is numeric 1
expect(parsed_option(parse_cli_args(spec, ["--count=3"]), "count").to_i64()).to_equal(3)  # oracle: parsed int option
```

</details>

#### multiple options together

#### parses flags and options together without cross-talk

- Verify: verbose flag, output option, and count option in one argv
   - Expected: parsed_flag(parsed, "verbose") is true
   - Expected: parsed_option(parsed, "count").to_i64() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: verbose flag, output option, and count option in one argv")
val spec = cli_spec_option(
    cli_spec_flag(cli_spec(), "verbose", "v", "verbose output"),
    "count", "c", "repeat count", "1", [])
val parsed = parse_cli_args(spec, ["--verbose", "--count=3"])
expect(parsed_flag(parsed, "verbose")).to_equal(true)  # oracle: flag set alongside options
expect(parsed_option(parsed, "count").to_i64()).to_equal(3)  # oracle: option parsed alongside flag
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `de9c2933dd71b2add9434b86a5a8c9c90f55ef2b99820cedc2a4e0a396291b4b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `de9c2933dd71b2add9434b86a5a8c9c90f55ef2b99820cedc2a4e0a396291b4b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `de9c2933dd71b2add9434b86a5a8c9c90f55ef2b99820cedc2a4e0a396291b4b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/feature/usage/cli_args_basic_spec.spl
mirror: doc/06_spec/feature/usage/cli_args_basic_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/cli_args_basic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/cli_args_basic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/cli_args_basic_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/feature/usage/cli_args_basic_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bool flag defaults to false and --verbose/-v set it true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cli_args_basic_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'string option keeps its default and accepts --key=value and --key value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cli_args_basic_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unrelated string option is unaffected by flag parsing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
