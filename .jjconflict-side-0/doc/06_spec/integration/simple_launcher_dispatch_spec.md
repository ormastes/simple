# Simple launcher dispatch regression spec

> Verifies the compiled `bin/simple` dispatches recognized subcommands in-process to

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple launcher dispatch regression spec

Verifies the compiled `bin/simple` dispatches recognized subcommands in-process to

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/simple_launcher_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies the compiled `bin/simple` dispatches recognized subcommands in-process to
their handlers, and treats an unrecognized first argument as a file path to run.

Post-self-hosting `bin/simple` is a compiled binary with an in-process CommandEntry
dispatch table (`src/app/cli/dispatch/table.spl`) — NOT the old shell wrapper that
copied itself and re-exec'd a runtime with `run <entrypoint.spl>`. This spec was
rewritten (#38) to test the current in-process routing instead of the removed
shell-wrapper mechanism (the old copy-text + fake-runtime + re-exec approach cannot
work against a compiled binary).

## Scenarios

### simple launcher dispatch (in-process)

#### dispatches the lint subcommand to its handler

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- dispatches the lint subcommand to its handler
   - Expected: out contains `Usage: simple lint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("dispatches the lint subcommand to its handler")
val (out, _err, _code) = run_simple(["lint"])
expect(out.contains("Usage: simple lint")).to_equal(true)
```

</details>

#### dispatches the fmt subcommand to its handler

- dispatches the fmt subcommand to its handler
   - Expected: out contains `Usage: simple fmt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("dispatches the fmt subcommand to its handler")
val (out, _err, _code) = run_simple(["fmt"])
expect(out.contains("Usage: simple fmt")).to_equal(true)
```

</details>

#### treats an unrecognized first argument as a file path to run

- treats an unrecognized first argument as a file path to run
   - Expected: (out + err) contains `file not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("treats an unrecognized first argument as a file path to run")
val (out, err, _code) = run_simple(["zz_not_a_command_launcher_spec.spl"])
expect((out + err).contains("file not found")).to_equal(true)
```

</details>

#### registers subcommands in the in-process dispatch table (no shell re-exec)

- registers subcommands in the in-process dispatch table (no shell re-exec)
   - Expected: table contains `get_command_table`
   - Expected: table contains `CommandEntry`
   - Expected: table contains `"lint"`
   - Expected: table contains `"fmt"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("registers subcommands in the in-process dispatch table (no shell re-exec)")
val table = rt_file_read_text("src/app/cli/dispatch/table.spl") ?? ""
expect(table.contains("get_command_table")).to_equal(true)
expect(table.contains("CommandEntry")).to_equal(true)
expect(table.contains("\"lint\"")).to_equal(true)
expect(table.contains("\"fmt\"")).to_equal(true)
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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a481d3246bfbe72db39b3e7f664cb0d257d3e92df63d5178d0f1fb61c4a1bcb3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a481d3246bfbe72db39b3e7f664cb0d257d3e92df63d5178d0f1fb61c4a1bcb3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a481d3246bfbe72db39b3e7f664cb0d257d3e92df63d5178d0f1fb61c4a1bcb3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/simple_launcher_dispatch_spec.spl
mirror: doc/06_spec/integration/simple_launcher_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/simple_launcher_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/simple_launcher_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/simple_launcher_dispatch_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches the lint subcommand to its handler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/simple_launcher_dispatch_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches the fmt subcommand to its handler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/simple_launcher_dispatch_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats an unrecognized first argument as a file path to run' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
