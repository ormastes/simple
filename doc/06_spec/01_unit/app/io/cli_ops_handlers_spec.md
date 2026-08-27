# Cli Ops Handlers Specification

> Tests covering Cli Ops Ext.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Ops Handlers Specification

## Scenarios

### Cli Ops Ext

#### reports missing context generation output for absent files

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports missing context generation output for absent files


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports missing context generation output for absent files")
val result = context_generate("path", "target", "format")
expect(result).to_contain("status: missing")
expect(result).to_contain("source: path")
expect(result).to_contain("target: target")
```

</details>

#### reports missing context stats output for absent files

- reports missing context stats output for absent files


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports missing context stats output for absent files")
val result = context_stats("path", "target")
expect(result).to_contain("status: missing")
expect(result).to_contain("source: path")
expect(result).to_contain("target: target")
```

</details>

#### returns success for settlement main placeholder implementation

- returns success for settlement main placeholder implementation
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns success for settlement main placeholder implementation")
val result = settlement_main()
expect(result).to_equal(0)
```

</details>

#### keeps fault configuration hooks callable without changing context stats

- keeps fault configuration hooks callable without changing context stats


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps fault configuration hooks callable without changing context stats")
fault_set_stack_overflow_detection(true)
fault_set_stack_overflow_detection(false)
fault_set_max_recursion_depth(100)
fault_set_timeout(30)
fault_set_execution_limit(1000)

expect(context_stats("path", "target")).to_contain("status: missing")
```

</details>

#### returns argument lists from both public argument accessors

- returns argument lists from both public argument accessors


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns argument lists from both public argument accessors")
val args = get_args()
val cli_args = cli_get_args()

expect(args.len()).to_be_greater_than(-1)
expect(cli_args.len()).to_be_greater_than(-1)
```

</details>

#### does not re-export the compiler-heavy CLI dispatch surface (regression guard)

- does not re-export the compiler-heavy CLI dispatch surface (regression guard)
   - Expected: source contains `fn cli_env_get`
   - Expected: source does not contain `export use app.io._CliCompile`
   - Expected: source does not contain `export use app.io._CliCommands.run_commands`
   - Expected: source does not contain `export use app.io._CliCommands.handler_commands`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not re-export the compiler-heavy CLI dispatch surface (regression guard)")
# cli_ops.spl is documented as "Pure Simple I/O" and is imported by
# light, broadly-used consumers like `app.io.mod` for basic helpers
# (shell, settlement_main, context_generate, ...). It previously ALSO
# re-exported `_CliCommands.run_commands`/`_CliCommands.handler_commands`/
# `_CliCompile.*` (cli_run_lint, cli_compile, cli_native_build, etc.) —
# duplicating what `app.io.cli_commands`/`app.io.cli_compile` already
# provide. Because the module loader's `export use` flattening pulls
# in a re-exported target's full transitive closure regardless of
# which names a caller actually requested, that duplication forced
# every consumer of `app.io.mod`/`app.io.cli_ops` — including simple
# test specs — to also compile the *entire* compiler (driver, lexer,
# HIR, MIR, every backend: ~250 files) on every invocation. See
# doc/08_tracking/bug/stage4_test_runner_daemon_fallback_relint_nonmemoized_2026-07-20.md.
# Guard: keep the compiler-dispatch re-exports out of this file so
# this regression can't silently come back.
val source = file_read("src/app/io/cli_ops.spl")
# Guard the guard: an empty read (e.g. run from the wrong CWD) would
# make every `.contains(...) == false` check below pass vacuously.
expect(source.contains("fn cli_env_get")).to_equal(true)
expect(source.contains("export use app.io._CliCompile")).to_equal(false)
expect(source.contains("export use app.io._CliCommands.run_commands")).to_equal(false)
expect(source.contains("export use app.io._CliCommands.handler_commands")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/cli_ops_handlers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Cli Ops Ext.
- Cli Ops Ext

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b7d5cba13eb2a725d10a1edd38c331d0e318a96286f822b7cfd0b47e922aa80f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b7d5cba13eb2a725d10a1edd38c331d0e318a96286f822b7cfd0b47e922aa80f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b7d5cba13eb2a725d10a1edd38c331d0e318a96286f822b7cfd0b47e922aa80f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **74/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/io/cli_ops_handlers_spec.spl
mirror: doc/06_spec/01_unit/app/io/cli_ops_handlers_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=40
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=74; blocker cap makes effective=49
doc/06_spec/01_unit/app/io/cli_ops_handlers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/io/cli_ops_handlers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/io/cli_ops_handlers_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/io/cli_ops_handlers_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/io/cli_ops_handlers_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/io/cli_ops_handlers_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports missing context generation output for absent files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/io/cli_ops_handlers_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports missing context stats output for absent files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/io/cli_ops_handlers_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns success for settlement main placeholder implementation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
