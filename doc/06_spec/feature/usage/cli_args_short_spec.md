# cli_args_short_spec

> Purpose: short-name behavior (explicit shorts, mixed-case shorts, conflicts,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cli_args_short_spec

Purpose: short-name behavior (explicit shorts, mixed-case shorts, conflicts,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | Active |
| Source | `test/feature/usage/cli_args_short_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: short-name behavior (explicit shorts, mixed-case shorts, conflicts,
bundled value forms) is exercised through the production parser
(std.nogc_sync_mut.cli.cli_parser). Audience: CLI engineers.

## Scenarios

### CLI Args Short Names

#### explicit short names

#### an explicit short name parses the flag it was declared for

- Verify: -t resolves the threads option declared with short t
   - Expected: parsed_option(parse_cli_args(spec, ["-t", "8"]), "threads") equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: -t resolves the threads option declared with short t")
val spec = cli_spec_option(cli_spec(), "threads", "t", "thread count", "4", [])
expect(parsed_option(parse_cli_args(spec, ["-t", "8"]), "threads")).to_equal("8")  # oracle: short + space value
```

</details>

#### an uppercase short name is distinct from its lowercase peer

- Verify: -C and -c address two different flags
   - Expected: parsed_flag(parsed, "color") is true
   - Expected: parsed_flag(parsed, "compact") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: -C and -c address two different flags")
val spec = cli_spec_flag(
    cli_spec_flag(cli_spec(), "color", "C", "colorize"), "compact", "c", "compact")
val parsed = parse_cli_args(spec, ["-C"])
expect(parsed_flag(parsed, "color")).to_equal(true)  # oracle: uppercase short hits color
expect(parsed_flag(parsed, "compact")).to_equal(false)  # oracle: lowercase flag untouched
```

</details>

#### conflict resolution

#### a short name not declared in the spec never matches an option

- Verify: undeclared short goes to remaining instead of binding
   - Expected: parsed_option(parsed, "count") equals `1`
   - Expected: parsed_remaining(parsed) contains `-x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: undeclared short goes to remaining instead of binding")
val spec = cli_spec_option(cli_spec(), "count", "c", "count", "1", [])
val parsed = parse_cli_args(spec, ["-x"])
expect(parsed_option(parsed, "count")).to_equal("1")  # oracle: count keeps default
expect(parsed_remaining(parsed).contains("-x")).to_equal(true)  # oracle: unknown short kept in remaining
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `6da82345d9855fa2744dca06ffa3e118d79509b146cf528fa106387e0f76e18d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6da82345d9855fa2744dca06ffa3e118d79509b146cf528fa106387e0f76e18d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6da82345d9855fa2744dca06ffa3e118d79509b146cf528fa106387e0f76e18d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/cli_args_short_spec.spl
mirror: doc/06_spec/feature/usage/cli_args_short_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/cli_args_short_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/cli_args_short_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/cli_args_short_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an explicit short name parses the flag it was declared for' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cli_args_short_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an uppercase short name is distinct from its lowercase peer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cli_args_short_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a short name not declared in the spec never matches an option' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
