# LLM Caret Messaging Phase 3/4 CLI Boundary

> Prove that the retained Phase 3 executable is honestly bootstrap-only, then require the source-matched Phase 4 executable to expose the production run, test, and Caret Messaging command surfaces. Carrier readiness is a separate scenario and cannot be inferred from command discovery.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Messaging Phase 3/4 CLI Boundary

Prove that the retained Phase 3 executable is honestly bootstrap-only, then require the source-matched Phase 4 executable to expose the production run, test, and Caret Messaging command surfaces. Carrier readiness is a separate scenario and cannot be inferred from command discovery.

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
| Updated | 2026-08-10 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Prove that the retained Phase 3 executable is honestly bootstrap-only, then
require the source-matched Phase 4 executable to expose the production run,
test, and Caret Messaging command surfaces. Carrier readiness is a separate
scenario and cannot be inferred from command discovery.

Set `SIMPLE_STAGE3_BINARY` and `SIMPLE_STAGE4_BINARY` to the exact retained
artifacts when they are outside the canonical bootstrap output tree.

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

Expected Phase 3 examples are `simple-bootstrap 1.0.0-beta` and
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

- Read the exact Phase 3 bootstrap identity
   - Expected: version_exit equals `0`
- Reject run test and Caret dispatch from Phase 3
   - Expected: run_exit equals `1`
   - Expected: test_exit equals `1`
   - Expected: caret_exit equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compiler = phase3_binary()
step("Read the exact Phase 3 bootstrap identity")
val (version_out, version_err, version_exit) = process_run(compiler, ["--version"])
expect(version_exit).to_equal(0)
expect(version_out + version_err).to_contain("simple-bootstrap")

step("Reject run test and Caret dispatch from Phase 3")
val (run_out, run_err, run_exit) = process_run(compiler, ["run", "--help"])
val (test_out, test_err, test_exit) = process_run(compiler, ["test", "--help"])
val (caret_out, caret_err, caret_exit) = process_run(compiler, ["caret", "--help"])
expect(run_exit).to_equal(1)
expect(run_out + run_err).to_contain("unknown command 'run'")
expect(test_exit).to_equal(1)
expect(test_out + test_err).to_contain("unknown command 'test'")
expect(caret_exit).to_equal(1)
expect(caret_out + caret_err).to_contain("unknown command 'caret'")
```

</details>

#### should require Phase 4 to run source, execute a spec, and expose Caret Messaging help

- Execute source through the exact Phase 4 full CLI
   - Expected: run_exit equals `0`
   - Expected: (run_out + run_err).trim() equals `5`
- Execute a real assertion through the Phase 4 test command
   - Expected: test_exit equals `0`
- Expose the production Caret Messaging command surface
   - Expected: help_exit equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compiler = phase4_binary()
step("Execute source through the exact Phase 4 full CLI")
val (run_out, run_err, run_exit) = process_run(
    compiler,
    ["run", "scripts/check/cert/redeploy_gate/fixtures/p2_add.spl"]
)
expect(run_exit).to_equal(0)
expect((run_out + run_err).trim()).to_equal("5")

step("Execute a real assertion through the Phase 4 test command")
val (test_out, test_err, test_exit) = process_run(
    compiler,
    ["test", "test/fixtures/app/llm_caret/messaging/phase4_cli_smoke_spec.spl",
        "--mode=interpreter", "--clean", "--fail-fast"]
)
expect(test_exit).to_equal(0)
expect(test_out + test_err).to_contain("1 passed")

step("Expose the production Caret Messaging command surface")
val (help_out, help_err, help_exit) = process_run(
    compiler,
    ["caret", "messaging", "--help"]
)
expect(help_exit).to_equal(0)
expect(help_out + help_err).to_contain("caret messaging status")
```

</details>

### REQ-LLM-MSG-016: compiled carrier admission

#### should require every Phase 4 Caret Messaging carrier to be provenance-ready

- Query readiness through the exact Phase 4 full CLI
   - Expected: status_exit equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Query readiness through the exact Phase 4 full CLI")
val (status_out, status_err, status_exit) = process_run(
    phase4_binary(),
    ["caret", "messaging", "status"]
)
val output = status_out + status_err
expect(status_exit).to_equal(0)
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
