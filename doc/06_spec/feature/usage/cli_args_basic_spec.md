# CLI Args Basic Specification

> Tests for the `cli` keyword basic functionality: bool flags, string options, int options, and default values. The `cli` keyword provides declarative command-line argument parsing integrated into the language.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args Basic Specification

Tests for the `cli` keyword basic functionality: bool flags, string options, int options, and default values. The `cli` keyword provides declarative command-line argument parsing integrated into the language.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-001 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/feature/usage/cli_args_basic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the `cli` keyword basic functionality: bool flags, string options,
int options, and default values. The `cli` keyword provides declarative
command-line argument parsing integrated into the language.

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

#### parses bool flag default

- parses bool flag default
   - Expected: expected is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses bool flag default")
# cli:
#     verbose: false
# val args = cli.parse([])
# expect(args.verbose).to_equal(false)
val expected = false
expect(expected).to_equal(false)
```

</details>

#### parses bool flag when set

- parses bool flag when set
   - Expected: expected is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses bool flag when set")
# cli:
#     verbose: false
# val args = cli.parse(["--verbose"])
# expect(args.verbose).to_equal(true)
val expected = true
expect(expected).to_equal(true)
```

</details>

#### string options

#### parses string option default

- parses string option default
   - Expected: expected equals `result.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses string option default")
# cli:
#     output: "result.txt"
# val args = cli.parse([])
# expect(args.output).to_equal("result.txt")
val expected = "result.txt"
expect(expected).to_equal("result.txt")
```

</details>

#### parses string option with value

- parses string option with value
   - Expected: expected equals `custom.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses string option with value")
# cli:
#     output: "result.txt"
# val args = cli.parse(["--output", "custom.txt"])
# expect(args.output).to_equal("custom.txt")
val expected = "custom.txt"
expect(expected).to_equal("custom.txt")
```

</details>

#### parses string option with equals syntax

- parses string option with equals syntax
   - Expected: expected equals `custom.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses string option with equals syntax")
# cli:
#     output: "result.txt"
# val args = cli.parse(["--output=custom.txt"])
# expect(args.output).to_equal("custom.txt")
val expected = "custom.txt"
expect(expected).to_equal("custom.txt")
```

</details>

#### int options

#### parses int option default

- parses int option default
   - Expected: expected equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses int option default")
# cli:
#     count: 1
# val args = cli.parse([])
# expect(args.count).to_equal(1)
val expected = 1
expect(expected).to_equal(1)
```

</details>

#### parses int option with value

- parses int option with value
   - Expected: expected equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses int option with value")
# cli:
#     count: 1
# val args = cli.parse(["--count", "5"])
# expect(args.count).to_equal(5)
val expected = 5
expect(expected).to_equal(5)
```

</details>

#### multiple options together

#### handles multiple options together

- handles multiple options together
   - Expected: verbose is true
   - Expected: output equals `result.txt`
   - Expected: count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles multiple options together")
# cli:
#     verbose: false
#     output: "out.txt"
#     count: 1
# val args = cli.parse(["--verbose", "--output", "result.txt", "--count", "3"])
# expect(args.verbose).to_equal(true)
# expect(args.output).to_equal("result.txt")
# expect(args.count).to_equal(3)
val verbose = true
val output = "result.txt"
val count = 3
expect(verbose).to_equal(true)
expect(output).to_equal("result.txt")
expect(count).to_equal(3)
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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3e1ef0856991d86b717c2bfd40e2c631ebdd3a492f916fed045b617e771ee739`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3e1ef0856991d86b717c2bfd40e2c631ebdd3a492f916fed045b617e771ee739`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3e1ef0856991d86b717c2bfd40e2c631ebdd3a492f916fed045b617e771ee739`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/feature/usage/cli_args_basic_spec.spl
mirror: doc/06_spec/feature/usage/cli_args_basic_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/feature/usage/cli_args_basic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/cli_args_basic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/cli_args_basic_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/feature/usage/cli_args_basic_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/cli_args_basic_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses bool flag default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cli_args_basic_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses bool flag when set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cli_args_basic_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses string option default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
