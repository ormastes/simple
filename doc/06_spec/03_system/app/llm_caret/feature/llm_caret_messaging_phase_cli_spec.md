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
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the llm caret messaging phase cli behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow

First retain the admitted Phase 3 path, hash, authority identity, and sanity
receipt. Run the Phase 3 scenario against that exact path; it must identify as
`simple-bootstrap` and must reject product-only commands instead of silently
routing them through `native-build`.

Next retain the frozen Phase 4 candidate path, hash, provenance record, and
essential-tools receipt. Run the Phase 4 scenario against that exact binary.
It must execute source, run a real test assertion, and expose the production
Caret Messaging help surface.

Finally build and probe the database, MCP, hook, bridge, and server carriers
with that same Phase 4 binary. The readiness scenario accepts only a zero exit
and five explicit `*-ready: true` rows backed by current provenance records.

## Syntax and examples

The canonical retained-artifact invocation is:

```text
SIMPLE_STAGE3_BINARY=/absolute/path/to/stage3/simple
SIMPLE_STAGE4_BINARY=/absolute/path/to/full/simple
/absolute/path/to/full/simple test <this-spec> --mode=interpreter --clean --fail-fast
```

Expected Phase 3 examples are `simple-bootstrap 1.0.0-RC` and
`error: unknown command 'caret'`. Expected Phase 4 examples are source output
`5`, a passing one-example SSpec summary, `caret messaging status` in help,
and `llm-caret-messaging: ready` after all five carriers are admitted.

## Failure interpretation

A missing binary, Rust seed, stale candidate, disabled stub guard, unknown
Phase 4 command, nonzero test result, or not-ready carrier is a failure. The
test deliberately does not fall back to Phase 3, raw source interpretation,
or artifact existence. Phase 3 success proves only bootstrap compilation;
Phase 4 command discovery proves only the product CLI; carrier readiness is a
separate runtime/provenance obligation.

## Evidence to retain

Keep the absolute Phase 3 and Phase 4 paths, SHA-256 values, source revision,
bootstrap manifest, and the complete stdout, stderr, and exit status for every
command. The Phase 4 receipt must also identify the compiler that produced the
full CLI and bind it to the admitted Phase 3 manifest. A copied executable with
no matching provenance is not acceptable evidence.

For each Caret carrier, retain its executable and provenance record together.
The status output is a summary, not a substitute for those records. Database,
MCP, hook, bridge, and server readiness must all come from artifacts generated
by the same Phase 4 candidate and current source tree.

## Isolation requirements

Run from a clean integration worktree. Use fresh output and cache directories;
do not reuse a cache produced by a Rust seed, a different source revision, or a
different Phase 3 executable. Keep `SIMPLE_NO_STUB_FALLBACK=1` active throughout
the build and carrier probes. Do not deploy the candidate merely to run this
test: select it explicitly with `SIMPLE_STAGE4_BINARY`.

The Phase 3 assertion is deliberately negative. Adding production commands to
the bootstrap-only binary would blur the trust boundary and must fail this
spec. Conversely, Phase 4 must not delegate its tested commands back to Phase
3 or to a raw source fallback.

## Acceptance boundary

This specification closes only the CLI and compiled-carrier portions of
REQ-LLM-MSG-013 and REQ-LLM-MSG-016. It does not establish credential-backed
Claude, Codex, or Gemini transport acceptance, performance targets, or release
readiness. Those remain subject to their dedicated system tests and receipts.

If Stage 4 is not admitted, keep the TODO blocked and report the Phase 3 audit
separately. Never convert the expected absence of `run`, `test`, and `caret` in
Phase 3 into a Phase 4 PASS.

## Scenarios

### LLM Caret Messaging Phase 3 and Phase 4 CLI boundary

### REQ-LLM-MSG-013: production CLI ownership

#### should keep Phase 3 bootstrap-only without misrouting full CLI commands

- should keep Phase 3 bootstrap-only without misrouting full CLI commands
- Read the exact Phase 3 bootstrap identity
   - Expected: version_exit equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
- Reject run test and Caret dispatch from Phase 3
   - Expected: run_exit equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: test_exit equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: caret_exit equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-LLM-MSG-013
# @req REQ-LLM-MSG-016
step("should keep Phase 3 bootstrap-only without misrouting full CLI commands")
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

- should require Phase 4 to run source, execute a spec, and expose Caret Messaging help
- Execute source through the exact Phase 4 full CLI
   - Expected: run_exit equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: (run_out + run_err).trim() equals `5`
- Execute a real assertion through the Phase 4 test command
   - Expected: test_exit equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
- Expose the production Caret Messaging command surface
   - Expected: help_exit equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require Phase 4 to run source, execute a spec, and expose Caret Messaging help")
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

- should require every Phase 4 Caret Messaging carrier to be provenance-ready
- Query readiness through the exact Phase 4 full CLI
   - Expected: status_exit equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require every Phase 4 Caret Messaging carrier to be provenance-ready")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-MSG-013`
- `REQ-LLM-MSG-016`
- `REQ-LLM-MSG-016.`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5b9de3be71512d5856ffc566d2954fa38dbbf0caa5180232777db1f96c6d9a10`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5b9de3be71512d5856ffc566d2954fa38dbbf0caa5180232777db1f96c6d9a10`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5b9de3be71512d5856ffc566d2954fa38dbbf0caa5180232777db1f96c6d9a10`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=85 oracle=70
  traceability=100 evidence=70 coverage=80 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl:1:1: advice SSDOC-COV-001 [coverage] (-20): the authored requirement defines adverse behavior but no adverse scenario is named
  why: Specifications should explain behavior outside the happy path.
  improve: Add adverse-path scenarios required by the source, or record a reasoned suppression.
test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl:130:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep Phase 3 bootstrap-only without misrouting full CLI commands' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep Phase 3 bootstrap-only without misrouting full CLI commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl:152:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require Phase 4 to run source, execute a spec, and expose Caret Messaging help' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require Phase 4 to run source, execute a spec, and expose Caret Messaging help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl:182:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require every Phase 4 Caret Messaging carrier to be provenance-ready' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl:182:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require every Phase 4 Caret Messaging carrier to be provenance-ready' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
