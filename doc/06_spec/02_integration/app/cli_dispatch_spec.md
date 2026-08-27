# Cli Dispatch Specification

> Tests covering pure-Simple CLI command dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Dispatch Specification

## Scenarios

### pure-Simple CLI command dispatch

#### derives inventory from the canonical command table

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- derives inventory from the canonical command table
   - Expected: command_count() equals `get_all_commands().len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("derives inventory from the canonical command table")
expect(command_count()).to_equal(get_all_commands().len())
expect(command_count()).to_be_greater_than(80)
```

</details>

#### reports every registered command as a Simple implementation

- reports every registered command as a Simple implementation
   - Expected: simple_impl_count() equals `command_count()`
   - Expected: coverage_percentage() equals `100.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports every registered command as a Simple implementation")
expect(simple_impl_count()).to_equal(command_count())
expect(coverage_percentage()).to_equal(100.0)
```

</details>

#### resolves representative developer tools

- resolves representative developer tools
   - Expected: entry == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("resolves representative developer tools")
val names = ["compile", "run", "test", "check", "lint", "fmt", "fix", "duplicate-check", "gen-lean"]
for name in names:
    val entry = find_command(name)
    expect(entry == nil).to_equal(false)
```

</details>

#### keeps production entries free of Rust override flags

- keeps production entries free of Rust override flags
   - Expected: entry.env_override equals ``
   - Expected: entry.needs_rust_flags.len() equals `0`
   - Expected: entry.has_simple_impl() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps production entries free of Rust override flags")
for name in get_all_commands():
    val entry = find_command(name).unwrap()
    expect(entry.env_override).to_equal("")
    expect(entry.needs_rust_flags.len()).to_equal(0)
    expect(entry.has_simple_impl()).to_equal(true)
```

</details>

#### routes test through the pure-Simple runner

- routes test through the pure-Simple runner
   - Expected: entry.app_path equals `src/app/test_runner_new/main.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("routes test through the pure-Simple runner")
val entry = find_command("test").unwrap()
expect(entry.app_path).to_equal("src/app/test_runner_new/main.spl")
```

</details>

#### fails lookup for unknown commands

- fails lookup for unknown commands
   - Expected: find_command("not-a-simple-command") == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails lookup for unknown commands")
expect(find_command("not-a-simple-command") == nil).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/cli_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pure-Simple CLI command dispatch.
- pure-Simple CLI command dispatch

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `833655a27e148ab42dc82d082cd480f8c9dbd67367d416c179ed03d4eeb99e3b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `833655a27e148ab42dc82d082cd480f8c9dbd67367d416c179ed03d4eeb99e3b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `833655a27e148ab42dc82d082cd480f8c9dbd67367d416c179ed03d4eeb99e3b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/02_integration/app/cli_dispatch_spec.spl
mirror: doc/06_spec/02_integration/app/cli_dispatch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/cli_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/cli_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/cli_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/cli_dispatch_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives inventory from the canonical command table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/cli_dispatch_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports every registered command as a Simple implementation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/cli_dispatch_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves representative developer tools' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
