# LLM Caret Messaging Phase 3/4 CLI Boundary

> Verifies the llm caret messaging phase cli behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Messaging Phase 3/4 CLI Boundary

Verifies the llm caret messaging phase cli behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/llm_caret_messaging.md |
| Plan | doc/03_plan/sys_test/llm_caret_messaging.md |
| Design | doc/05_design/app/tools/llm_caret_messaging.md |
| Research | doc/01_research/app/llm_caret/messaging_platforms.md |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the llm caret messaging phase cli behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### LLM Caret Messaging Phase 3 and Phase 4 CLI boundary

### REQ-LLM-MSG-013: production CLI ownership

#### should keep Phase 3 bootstrap-only without misrouting full CLI commands

- Verify: should keep Phase 3 bootstrap-only without misrouting full CLI commands
- Read the exact Phase 3 bootstrap identity
   - Expected: version_exit equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
- Reject run test and Caret dispatch from Phase 3
   - Expected: run_exit equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: test_exit equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: caret_exit equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-013 REQ-LLM-MSG-016 REQ-LLM-MSG-016.
step("Verify: should keep Phase 3 bootstrap-only without misrouting full CLI commands")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val compiler = phase3_binary()
step("Read the exact Phase 3 bootstrap identity")
val (version_out, version_err, version_exit) = process_run(compiler, ["--version"])
expect(version_exit).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(version_out + version_err).to_contain("simple-bootstrap")

step("Reject run test and Caret dispatch from Phase 3")
val (run_out, run_err, run_exit) = process_run(compiler, ["run", "--help"])
val (test_out, test_err, test_exit) = process_run(compiler, ["test", "--help"])
val (caret_out, caret_err, caret_exit) = process_run(compiler, ["caret", "--help"])
expect(run_exit).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(run_out + run_err).to_contain("unknown command 'run'")
expect(test_exit).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(test_out + test_err).to_contain("unknown command 'test'")
expect(caret_exit).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(caret_out + caret_err).to_contain("unknown command 'caret'")
```

</details>

#### should require Phase 4 to run source, execute a spec, and expose Caret Messaging help

- Verify: should require Phase 4 to run source, execute a spec, and expose Caret Messaging help
- Execute source through the exact Phase 4 full CLI
   - Expected: run_exit equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: (run_out + run_err).trim() equals `5`
- Execute a real assertion through the Phase 4 test command
   - Expected: test_exit equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
- Expose the production Caret Messaging command surface
   - Expected: help_exit equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-013 REQ-LLM-MSG-016
step("Verify: should require Phase 4 to run source, execute a spec, and expose Caret Messaging help")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val compiler = phase4_binary()
step("Execute source through the exact Phase 4 full CLI")
val (run_out, run_err, run_exit) = process_run(
    compiler,
    ["run", "scripts/check/cert/redeploy_gate/fixtures/p2_add.spl"]
)
expect(run_exit).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect((run_out + run_err).trim()).to_equal("5")

step("Execute a real assertion through the Phase 4 test command")
val (test_out, test_err, test_exit) = process_run(
    compiler,
    ["test", "test/fixtures/app/llm_caret/messaging/phase4_cli_smoke_spec.spl",
        "--mode=interpreter", "--clean", "--fail-fast"]
)
expect(test_exit).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(test_out + test_err).to_contain("1 passed")

step("Expose the production Caret Messaging command surface")
val (help_out, help_err, help_exit) = process_run(
    compiler,
    ["caret", "messaging", "--help"]
)
expect(help_exit).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(help_out + help_err).to_contain("caret messaging status")
```

</details>

### REQ-LLM-MSG-016: compiled carrier admission

#### should require every Phase 4 Caret Messaging carrier to be provenance-ready

- Verify: should require every Phase 4 Caret Messaging carrier to be provenance-ready
- Query readiness through the exact Phase 4 full CLI
   - Expected: status_exit equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-013 REQ-LLM-MSG-016
step("Verify: should require every Phase 4 Caret Messaging carrier to be provenance-ready")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Query readiness through the exact Phase 4 full CLI")
val (status_out, status_err, status_exit) = process_run(
    phase4_binary(),
    ["caret", "messaging", "status"]
)
val output = status_out + status_err
expect(status_exit).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(output).to_contain("llm-caret-messaging: ready")
expect(output).to_contain("database-ready: true")
expect(output).to_contain("mcp-ready: true")
expect(output).to_contain("hook-ready: true")
expect(output).to_contain("bridge-ready: true")
expect(output).to_contain("server-ready: true")
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


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/llm_caret_messaging.md`
- **Plan:** `doc/03_plan/sys_test/llm_caret_messaging.md`
- **Design:** `doc/05_design/app/tools/llm_caret_messaging.md`
- **Research:** `doc/01_research/app/llm_caret/messaging_platforms.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3538307a81429a78345b4c6d12b2ba664e5ab666e80d5cd14e26d67dc3fbc2c6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3538307a81429a78345b4c6d12b2ba664e5ab666e80d5cd14e26d67dc3fbc2c6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3538307a81429a78345b4c6d12b2ba664e5ab666e80d5cd14e26d67dc3fbc2c6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=85 coverage=80 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl:1:1: advice SSDOC-COV-001 [coverage] (-20): the authored requirement defines adverse behavior but no adverse scenario is named
  why: Specifications should explain behavior outside the happy path.
  improve: Add adverse-path scenarios required by the source, or record a reasoned suppression.
test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl:140:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep Phase 3 bootstrap-only without misrouting full CLI commands' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl:161:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require Phase 4 to run source, execute a spec, and expose Caret Messaging help' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl:192:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require every Phase 4 Caret Messaging carrier to be provenance-ready' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
