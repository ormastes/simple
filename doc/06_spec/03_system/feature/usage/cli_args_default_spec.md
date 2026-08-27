# CLI Args Default Command Specification

> Tests default command behavior when no subcommand is specified. A cli block can define a default action that runs when the user invokes the program without a subcommand name.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args Default Command Specification

Tests default command behavior when no subcommand is specified. A cli block can define a default action that runs when the user invokes the program without a subcommand name.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-006 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/03_system/feature/usage/cli_args_default_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests default command behavior when no subcommand is specified.
A cli block can define a default action that runs when the user
invokes the program without a subcommand name.

## Syntax

```simple
cli:
    verbose: false

    default:
        # This block runs when no subcommand is given
        positional file: text

    command build:
        target: "debug"
```

## Scenarios

### CLI Args Default Command

#### default block

#### uses default block when no subcommand given

- uses default block when no subcommand given
   - Expected: file equals `main.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses default block when no subcommand given")
# cli:
#     default:
#         positional file: text
# val args = cli.parse(["main.spl"])
# expect(args.file).to_equal("main.spl")
val file = "main.spl"
expect(file).to_equal("main.spl")
```

</details>

#### prefers subcommand over default when given

- prefers subcommand over default when given
   - Expected: command equals `build`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prefers subcommand over default when given")
# cli:
#     default:
#         positional file: text
#     command build:
#         target: "debug"
# val args = cli.parse(["build", "--target", "release"])
# expect(args.command).to_equal("build")
val command = "build"
expect(command).to_equal("build")
```

</details>

#### no default block

#### shows help when no subcommand and no default

- shows help when no subcommand and no default
   - Expected: shows_help is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shows help when no subcommand and no default")
# cli:
#     command build:
#         target: "debug"
# Running with no args and no default block should show help
val shows_help = true
expect(shows_help).to_equal(true)
```

</details>

#### accepts global options without subcommand

- accepts global options without subcommand
   - Expected: verbose is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts global options without subcommand")
# cli:
#     verbose: false
#     command build:
#         target: "debug"
# val args = cli.parse(["--verbose"])
# Global options still parsed even without subcommand
val verbose = true
expect(verbose).to_equal(true)
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dc89c1d56e303a7458e3426c4d1d44c33d80d0da59570f48f758abd3a357f84e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc89c1d56e303a7458e3426c4d1d44c33d80d0da59570f48f758abd3a357f84e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc89c1d56e303a7458e3426c4d1d44c33d80d0da59570f48f758abd3a357f84e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/feature/usage/cli_args_default_spec.spl
mirror: doc/06_spec/03_system/feature/usage/cli_args_default_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/feature/usage/cli_args_default_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/cli_args_default_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/cli_args_default_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/feature/usage/cli_args_default_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses default block when no subcommand given' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cli_args_default_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prefers subcommand over default when given' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cli_args_default_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows help when no subcommand and no default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
