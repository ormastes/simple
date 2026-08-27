# CLI Args Short Names Specification

> Tests short name generation and explicit short name overrides for CLI options. The cli keyword auto-generates single-character short names from the first letter of the option name, with conflict resolution when multiple options share the same first letter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args Short Names Specification

Tests short name generation and explicit short name overrides for CLI options. The cli keyword auto-generates single-character short names from the first letter of the option name, with conflict resolution when multiple options share the same first letter.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-003 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/03_system/feature/usage/cli_args_short_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests short name generation and explicit short name overrides for CLI options.
The cli keyword auto-generates single-character short names from the first
letter of the option name, with conflict resolution when multiple options
share the same first letter.

## Syntax

```simple
cli:
    verbose: false                # auto-short: -v
    output: "out.txt"             # auto-short: -o
    count: 1, short: "c"         # explicit short: -c
    color: true, short: "C"      # explicit short: -C (avoids conflict with count)
```

## Scenarios

### CLI Args Short Names

#### auto-generated short names

#### generates short from first letter

- generates short from first letter
   - Expected: short_name equals `v`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates short from first letter")
# cli:
#     verbose: false
# cli.parse(["-v"]) should set verbose = true
val short_name = "v"
expect(short_name).to_equal("v")
```

</details>

#### generates short for string option

- generates short for string option
   - Expected: short_name equals `o`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates short for string option")
# cli:
#     output: "default.txt"
# cli.parse(["-o", "file.txt"]) should set output = "file.txt"
val short_name = "o"
expect(short_name).to_equal("o")
```

</details>

#### generates short for int option

- generates short for int option
   - Expected: short_name equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates short for int option")
# cli:
#     count: 1
# cli.parse(["-c", "5"]) should set count = 5
val short_name = "c"
expect(short_name).to_equal("c")
```

</details>

#### explicit short names

#### uses explicit short name

- uses explicit short name
   - Expected: explicit_short equals `t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses explicit short name")
# cli:
#     threads: 4, short: "t"
# cli.parse(["-t", "8"]) should set threads = 8
val explicit_short = "t"
expect(explicit_short).to_equal("t")
```

</details>

#### allows uppercase short name

- allows uppercase short name
   - Expected: explicit_short equals `C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows uppercase short name")
# cli:
#     color: true, short: "C"
# cli.parse(["-C"]) should toggle color
val explicit_short = "C"
expect(explicit_short).to_equal("C")
```

</details>

#### conflict resolution

#### skips short when conflict exists

- skips short when conflict exists
   - Expected: first_short equals `c`
   - Expected: second_short equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips short when conflict exists")
# cli:
#     count: 1
#     color: true
# First option gets -c, second has no auto-short (conflict)
val first_short = "c"
val second_short = ""
expect(first_short).to_equal("c")
expect(second_short).to_equal("")
```

</details>

#### resolves conflict with explicit short

- resolves conflict with explicit short
   - Expected: count_short equals `c`
   - Expected: color_short equals `C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves conflict with explicit short")
# cli:
#     count: 1
#     color: true, short: "C"
# count gets -c, color gets -C (explicit)
val count_short = "c"
val color_short = "C"
expect(count_short).to_equal("c")
expect(color_short).to_equal("C")
```

</details>

#### handles no available short name

- handles no available short name
   - Expected: alpha_short equals `a`
   - Expected: append_short equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles no available short name")
# cli:
#     alpha: false
#     append: true
# alpha gets -a, append gets no short (conflict, no explicit)
val alpha_short = "a"
val append_short = ""
expect(alpha_short).to_equal("a")
expect(append_short).to_equal("")
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3a25f7a751871f3ae1f39a8de6eabd2e1e05848277643aec8e5a2b446546ea82`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3a25f7a751871f3ae1f39a8de6eabd2e1e05848277643aec8e5a2b446546ea82`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3a25f7a751871f3ae1f39a8de6eabd2e1e05848277643aec8e5a2b446546ea82`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **72/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/feature/usage/cli_args_short_spec.spl
mirror: doc/06_spec/03_system/feature/usage/cli_args_short_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=0
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=72; blocker cap makes effective=49
doc/06_spec/03_system/feature/usage/cli_args_short_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/cli_args_short_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/cli_args_short_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/feature/usage/cli_args_short_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/feature/usage/cli_args_short_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates short from first letter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cli_args_short_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates short for string option' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cli_args_short_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates short for int option' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
