# CLI Args Default Command Specification

> Exercises default/fallback argument behavior (bare positionals, global flags without a command, help generation) through the real parser (std.nogc_sync_mut.cli.cli_parser). The parser's contract: with no subcommand grammar, the first bare word is the first positional and unknown dashed tokens fall into `remaining`, so help/validate report them.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args Default Command Specification

Exercises default/fallback argument behavior (bare positionals, global flags without a command, help generation) through the real parser (std.nogc_sync_mut.cli.cli_parser). The parser's contract: with no subcommand grammar, the first bare word is the first positional and unknown dashed tokens fall into `remaining`, so help/validate report them.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-006 |
| Category | Language \| CLI |
| Status | Implemented |
| Source | `test/feature/usage/cli_args_default_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exercises default/fallback argument behavior (bare positionals, global flags
without a command, help generation) through the real parser
(std.nogc_sync_mut.cli.cli_parser). The parser's contract: with no
subcommand grammar, the first bare word is the first positional and unknown
dashed tokens fall into `remaining`, so help/validate report them.

## Scenarios

### CLI Args Default Command

#### default block

#### first bare word fills the default positional slot

- Verify: bare word becomes the default positional
   - Expected: parsed_positional(parsed, 0) equals `main.spl`
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: bare word becomes the default positional")
val spec = cli_spec_positional(cli_spec(), "file", "input file", true)
val parsed = parse_cli_args(spec, ["main.spl"])
expect(parsed_positional(parsed, 0)).to_equal("main.spl")  # oracle: default slot takes the bare word
val (valid, message) = validate_args(spec, parsed)
expect(valid).to_equal(true)  # oracle: required positional satisfied
```

</details>

#### a leading dashed token is not consumed as the positional

- Verify: option-looking token routes to remaining, not positionals
   - Expected: parsed_positional(parsed, 0) equals `release`
   - Expected: parsed_remaining(parsed) contains `--target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: option-looking token routes to remaining, not positionals")
val spec = cli_spec_positional(cli_spec(), "file", "input file", true)
val parsed = parse_cli_args(spec, ["--target", "release"])
expect(parsed_positional(parsed, 0)).to_equal("release")  # oracle: value word is the first positional
expect(parsed_remaining(parsed).contains("--target")).to_equal(true)  # oracle: dashed token kept in remaining
```

</details>

#### no default block

#### validation fails closed when a required positional is missing

- Verify: empty argv with a required positional is invalid, so help is shown
   - Expected: valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: empty argv with a required positional is invalid, so help is shown")
val spec = cli_spec_positional(cli_spec(), "file", "input file", true)
val parsed = parse_cli_args(spec, [])
val (valid, message) = validate_args(spec, parsed)
expect(valid).to_equal(false)  # oracle: missing required positional rejected
expect(message).to_contain("file")  # oracle: message names the missing positional
```

</details>

#### global flags still parse when no positional is given

- Verify: --verbose alone sets the flag
   - Expected: parsed_flag(parse_cli_args(spec, ["--verbose"]), "verbose") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: --verbose alone sets the flag")
val spec = cli_spec_flag(cli_spec(), "verbose", "v", "verbose output")
expect(parsed_flag(parse_cli_args(spec, ["--verbose"]), "verbose")).to_equal(true)  # oracle: flag parsed without positional
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `65c8ecc6219fcea281a6dc639ff3770e3af2cbf8133844bcd122d9094849a975`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `65c8ecc6219fcea281a6dc639ff3770e3af2cbf8133844bcd122d9094849a975`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `65c8ecc6219fcea281a6dc639ff3770e3af2cbf8133844bcd122d9094849a975`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/feature/usage/cli_args_default_spec.spl
mirror: doc/06_spec/feature/usage/cli_args_default_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/cli_args_default_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/cli_args_default_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/cli_args_default_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/feature/usage/cli_args_default_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'first bare word fills the default positional slot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cli_args_default_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a leading dashed token is not consumed as the positional' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cli_args_default_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validation fails closed when a required positional is missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
