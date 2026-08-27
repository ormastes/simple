# CLI Help Text Alignment Specification

> The Simple CLI keeps its command list by hand in several places. Only ONE of them actually executes: the `str_eq(first, "...")` chain in `src/app/cli/_CliMain/main_and_help.spl`. The help text (`cli_helpers.spl print_cli_help()`) and the dispatch table (`src/app/cli/dispatch/table.spl`) are separate hand-written lists that drift away from it silently.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Help Text Alignment Specification

The Simple CLI keeps its command list by hand in several places. Only ONE of them actually executes: the `str_eq(first, "...")` chain in `src/app/cli/_CliMain/main_and_help.spl`. The help text (`cli_helpers.spl print_cli_help()`) and the dispatch table (`src/app/cli/dispatch/table.spl`) are separate hand-written lists that drift away from it silently.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #3026-3030 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/unit/app/cli_help_alignment_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The Simple CLI keeps its command list by hand in several places. Only ONE of
them actually executes: the `str_eq(first, "...")` chain in
`src/app/cli/_CliMain/main_and_help.spl`. The help text
(`cli_helpers.spl print_cli_help()`) and the dispatch table
(`src/app/cli/dispatch/table.spl`) are separate hand-written lists that drift
away from it silently.

This spec READS those three sources and COUNTS. It does not hardcode counts.
Every number below is derived from the files at run time, so a command added
to or removed from any of the three lists changes the measurement.

The executing elif chain is the oracle. "Phantom" and "dead entry" are both
defined relative to it.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Dispatch command | A `str_eq(first, "X")` branch — the only list that runs |
| Help command | A command printed by `print_cli_help()` |
| Table command | A `CommandEntry(name: "X"` in `dispatch/table.spl` |
| Phantom command | Advertised in help but absent from dispatch — user hits an error |
| Dead table entry | In the table but absent from dispatch — unreachable data |
| Undocumented command | Dispatchable but never mentioned in help |

## Related Specifications

- [CLI Command Inventory](cli_command_inventory_spec.spl)
- [CLI Dispatch Unit Tests](cli_dispatch_unit_spec.spl)

## Scenarios

### CLI alignment — extraction is real

#### all three CLI sources exist

- all three CLI sources exist
   - Expected: file_exists(DISPATCH_SRC) is true
   - Expected: file_exists(HELP_SRC) is true
   - Expected: file_exists(TABLE_SRC) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all three CLI sources exist")
expect(file_exists(DISPATCH_SRC)).to_equal(true)
expect(file_exists(HELP_SRC)).to_equal(true)
expect(file_exists(TABLE_SRC)).to_equal(true)
```

</details>

#### each extractor returns a plausibly-sized command set

- each extractor returns a plausibly-sized command set


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("each extractor returns a plausibly-sized command set")
# Floors are deliberately far below the measured sizes (dispatch 103,
# table 84, help 58 on 2026-08-11). They catch a broken extractor,
# not ordinary command churn.
expect(extract_dispatch_commands().len()).to_be_greater_than(50)
expect(extract_table_commands().len()).to_be_greater_than(40)
expect(extract_help_commands().len()).to_be_greater_than(20)
```

</details>

#### known-good commands are found in every list that should hold them

- known-good commands are found in every list that should hold them
   - Expected: extract_dispatch_commands() contains `cmd`
   - Expected: extract_table_commands() contains `cmd`
   - Expected: extract_help_commands() contains `cmd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("known-good commands are found in every list that should hold them")
# Anchor probe: these are present in ALL THREE sources (verified by
# set intersection on 2026-08-11). If the extractors regress to
# returning junk tokens, these named lookups fail even though the
# counts might still look plausible.
# NOTE deliberately excludes `run`: help advertises running a file as
# `simple <file.spl>`, so `run` is legitimately absent from help.
for cmd in ["compile", "build", "check"]:
    expect(extract_dispatch_commands().contains(cmd)).to_equal(true)
    expect(extract_table_commands().contains(cmd)).to_equal(true)
    expect(extract_help_commands().contains(cmd)).to_equal(true)
```

</details>

#### flags and placeholders are not mistaken for commands

- flags and placeholders are not mistaken for commands
   - Expected: help does not contain `--notui`
   - Expected: help does not contain `-c`
   - Expected: help does not contain `<file.spl>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags and placeholders are not mistaken for commands")
val help = extract_help_commands()
expect(help.contains("--notui")).to_equal(false)
expect(help.contains("-c")).to_equal(false)
expect(help.contains("<file.spl>")).to_equal(false)
```

</details>

### CLI No Phantom Commands

#### every command in help text has a dispatch branch

- every command in help text has a dispatch branch
   - Expected: phantoms equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every command in help text has a dispatch branch")
"""MEASURED 2026-08-11: was RED with 1 phantom, `check-capsule`. Fixed
by wiring the existing `handle_check_capsule` implementation into the
dispatch chain. See
doc/08_tracking/bug/cli_help_dispatch_drift_2026-08-11.md.
Do not delete this assertion to obtain green; fix help or dispatch."""
val phantoms = missing_from(extract_help_commands(),
    extract_dispatch_commands())
expect(phantoms).to_equal([])
```

</details>

### CLI Dispatch Table Reachability

#### every dispatch-table entry has a dispatch branch

- every dispatch-table entry has a dispatch branch
   - Expected: dead equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every dispatch-table entry has a dispatch branch")
"""MEASURED 2026-08-11: was RED with 24 unreachable table entries.
Fixed: 22 were wired into the dispatch chain (every implementation was
verified present), `bench` was deleted from the table (its app no
longer exists), and `native-build` was never really dead — it is
dispatched before the chain and the extractor now sees it. See
doc/08_tracking/bug/cli_help_dispatch_drift_2026-08-11.md."""
val dead = missing_from(extract_table_commands(),
    extract_dispatch_commands())
expect(dead).to_equal([])
```

</details>

### CLI Help Coverage Ratchet

#### the undocumented-command count does not exceed its baseline

- the undocumented-command count does not exceed its baseline


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the undocumented-command count does not exceed its baseline")
val undocumented = missing_from(extract_dispatch_commands(),
    extract_help_commands())
expect(undocumented.len()).to_be_less_than(UNDOCUMENTED_BASELINE + 1)
```

</details>

#### every dispatchable command is advertised in help text

- every dispatchable command is advertised in help text
   - Expected: undocumented equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every dispatchable command is advertised in help text")
# Exact equality, not a bound: names the offenders when it fails.
val undocumented = missing_from(extract_dispatch_commands(),
    extract_help_commands())
expect(undocumented).to_equal([])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `8cab5135217d5017d34748edc90b5da770823bfd615992a93ebf3f97304698fd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8cab5135217d5017d34748edc90b5da770823bfd615992a93ebf3f97304698fd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8cab5135217d5017d34748edc90b5da770823bfd615992a93ebf3f97304698fd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/cli_help_alignment_spec.spl
mirror: doc/06_spec/unit/app/cli_help_alignment_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/cli_help_alignment_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/cli_help_alignment_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/cli_help_alignment_spec.spl:175:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all three CLI sources exist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli_help_alignment_spec.spl:182:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'each extractor returns a plausibly-sized command set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli_help_alignment_spec.spl:192:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'known-good commands are found in every list that should hold them' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
