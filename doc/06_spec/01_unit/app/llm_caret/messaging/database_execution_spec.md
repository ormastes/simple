# Database Execution Specification

> Tests covering messaging database execution policy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database Execution Specification

## Scenarios

### messaging database execution policy

#### uses a cached native executable even for an interpreter-hosted caller

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses a cached native executable even for an interpreter-hosted caller
   - Expected: plan.kind equals `DatabaseArtifactKind.NativeExecutable`
   - Expected: plan.artifact_path equals `build/database/llm_caret_messaging_db`
   - Expected: plan.requires_fresh_artifact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses a cached native executable even for an interpreter-hosted caller")
val plan = interpreter_fallback_plan(false)
expect(plan.kind).to_equal(DatabaseArtifactKind.NativeExecutable)
expect(plan.artifact_path).to_equal("build/database/llm_caret_messaging_db")
expect(plan.requires_fresh_artifact).to_equal(true)
```

</details>

#### permits interpreted source only as an explicit diagnostic fallback

- permits interpreted source only as an explicit diagnostic fallback
   - Expected: plan.kind equals `DatabaseArtifactKind.InterpretedSource`
   - Expected: plan.reason equals `explicit_diagnostic_fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("permits interpreted source only as an explicit diagnostic fallback")
val plan = interpreter_fallback_plan(true)
expect(plan.kind).to_equal(DatabaseArtifactKind.InterpretedSource)
expect(plan.reason).to_equal("explicit_diagnostic_fallback")
```

</details>

#### keeps an interpreter-hosted caller on a compiled database carrier

- keeps an interpreter-hosted caller on a compiled database carrier
   - Expected: database_should_use_compiled_carrier(true, false) is true
   - Expected: database_should_use_compiled_carrier(false, false) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps an interpreter-hosted caller on a compiled database carrier")
expect(database_should_use_compiled_carrier(true, false)).to_equal(true)
expect(database_should_use_compiled_carrier(false, false)).to_equal(true)
```

</details>

#### allows source interpretation only after an explicit diagnostic request

- allows source interpretation only after an explicit diagnostic request
   - Expected: database_should_use_compiled_carrier(true, true) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("allows source interpretation only after an explicit diagnostic request")
expect(database_should_use_compiled_carrier(true, true)).to_equal(false)
```

</details>

#### can select a cached native database executable

- can select a cached native database executable
   - Expected: plan.kind equals `DatabaseArtifactKind.NativeExecutable`
   - Expected: plan.artifact_path equals `build/database/llm_caret_messaging_db`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("can select a cached native database executable")
val plan = default_database_execution_plan(true)
expect(plan.kind).to_equal(DatabaseArtifactKind.NativeExecutable)
expect(plan.artifact_path).to_equal("build/database/llm_caret_messaging_db")
```

</details>

#### builds and executes the SMF carrier instead of interpreting database source

- builds and executes the SMF carrier instead of interpreting database source
- Select the normal database carrier for an interpreter-hosted caller
   - Expected: build.command equals `bin/simple`
   - Expected: build.args equals `["compile", "src/app/llm_caret/messaging/database_worker.spl",`
   - Expected: run.command equals `bin/simple`
   - Expected: run.args[0] equals `run`
   - Expected: run.args[1] equals `build/database/llm_caret_messaging_db.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("builds and executes the SMF carrier instead of interpreting database source")
step("Select the normal database carrier for an interpreter-hosted caller")
val plan = default_database_execution_plan(false)
val build = database_artifact_build_command(plan, "bin/simple")
val run = database_artifact_run_command(plan, "bin/simple",
    ["--operation", "probe", "--db", "/tmp/messages.pdb"])
expect(build.command).to_equal("bin/simple")
expect(build.args).to_equal(["compile", "src/app/llm_caret/messaging/database_worker.spl",
    "-o", "build/database/llm_caret_messaging_db.smf"])
expect(run.command).to_equal("bin/simple")
expect(run.args[0]).to_equal("run")
expect(run.args[1]).to_equal("build/database/llm_caret_messaging_db.smf")
```

</details>

#### executes the native carrier directly when native is selected

- executes the native carrier directly when native is selected
   - Expected: run.command equals `build/database/llm_caret_messaging_db`
   - Expected: run.args equals `["--operation", "probe"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("executes the native carrier directly when native is selected")
val plan = default_database_execution_plan(true)
val run = database_artifact_run_command(plan, "bin/simple", ["--operation", "probe"])
expect(run.command).to_equal("build/database/llm_caret_messaging_db")
expect(run.args).to_equal(["--operation", "probe"])
```

</details>

#### runs MCP and PureDatabase together in the cached native worker

- runs MCP and PureDatabase together in the cached native worker
   - Expected: plan.kind equals `DatabaseArtifactKind.NativeExecutable`
   - Expected: plan.source_path equals `src/app/llm_caret/messaging/mcp_worker.spl`
   - Expected: plan.artifact_path equals `build/database/llm_caret_messaging_mcp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("runs MCP and PureDatabase together in the cached native worker")
val plan = default_messaging_mcp_execution_plan(true)
val build = database_artifact_build_command(plan, "bin/simple")
expect(plan.kind).to_equal(DatabaseArtifactKind.NativeExecutable)
expect(plan.source_path).to_equal("src/app/llm_caret/messaging/mcp_worker.spl")
expect(plan.artifact_path).to_equal("build/database/llm_caret_messaging_mcp")
expect(build.args).to_contain("--entry-closure")
```

</details>

#### runs the primitive server and database in one cached native worker

- runs the primitive server and database in one cached native worker
   - Expected: plan.kind equals `DatabaseArtifactKind.NativeExecutable`
   - Expected: plan.source_path equals `src/app/llm_caret/messaging/server_worker.spl`
   - Expected: plan.artifact_path equals `build/database/llm_caret_messaging_server`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("runs the primitive server and database in one cached native worker")
val plan = default_messaging_server_execution_plan(true)
expect(plan.kind).to_equal(DatabaseArtifactKind.NativeExecutable)
expect(plan.source_path).to_equal("src/app/llm_caret/messaging/server_worker.spl")
expect(plan.artifact_path).to_equal("build/database/llm_caret_messaging_server")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/database_execution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering messaging database execution policy.
- messaging database execution policy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3e7c86d2c8e1e68ae64186c68953e1e0c1aa744239a84d9de94817fe00628caf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3e7c86d2c8e1e68ae64186c68953e1e0c1aa744239a84d9de94817fe00628caf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3e7c86d2c8e1e68ae64186c68953e1e0c1aa744239a84d9de94817fe00628caf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/app/llm_caret/messaging/database_execution_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/database_execution_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/messaging/database_execution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/database_execution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/database_execution_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses a cached native executable even for an interpreter-hosted caller' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/database_execution_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'permits interpreted source only as an explicit diagnostic fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/database_execution_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps an interpreter-hosted caller on a compiled database carrier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/database_execution_spec.spl:50:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can select a cached native database executable' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
