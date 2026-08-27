# LLM Caret CLI Process Hardening

> Runs the actual Caret command entrypoint through the self-hosted `bin/simple` runtime and separately verifies that the production `bin/caret` wrapper selects an explicit cached executable, forwards arguments, and fails closed on an invalid override. A fixture configuration routes the Claude provider to a deterministic local executable, so success, subprocess failure, help, and argument rejection are verified without credentials, network access, or paid calls.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret CLI Process Hardening

Runs the actual Caret command entrypoint through the self-hosted `bin/simple` runtime and separately verifies that the production `bin/caret` wrapper selects an explicit cached executable, forwards arguments, and fails closed on an invalid override. A fixture configuration routes the Claude provider to a deterministic local executable, so success, subprocess failure, help, and argument rejection are verified without credentials, network access, or paid calls.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md |
| Plan | doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md |
| Design | doc/05_design/llm_caret_claude_cli_full_parity.md |
| Research | doc/01_research/local/llm_caret_claude_cli_harden.md |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Runs the actual Caret command entrypoint through the self-hosted `bin/simple`
runtime and separately verifies that the production `bin/caret` wrapper selects
an explicit cached executable, forwards arguments, and fails closed on an
invalid override. A fixture configuration routes the Claude provider to a
deterministic local executable, so success, subprocess failure, help, and
argument rejection are verified without credentials, network access, or paid
calls.

## Scope

This specification covers the application process boundary that pure provider
tests cannot prove:

- the self-hosted runtime starts the Caret source entrypoint for component
  process checks;
- the production wrapper selects a cached native executable rather than
  silently running source;
- an invalid explicit cached-artifact override fails closed;
- `--help` reaches Caret rather than the compiler help surface;
- a fixture SDN configuration selects the local Claude executable;
- explicit provider, model, system prompt, and one-shot prompt options parse;
- the application reaches the production provider dispatcher;
- the provider reaches the shared Claude CLI wrapper;
- removed automatic flags do not reach the child process;
- structured fixture JSON reaches the final printed response;
- nonzero child exits become nonzero Caret exits;
- child stderr secrets are redacted before display;
- an unknown Caret option returns the documented usage exit.

The test deliberately does not validate remote authentication, model quality,
billing, network availability, terminal pixels, or interactive input timing.
Those concerns belong to opt-in live and TUI evidence lanes.

## Process Matrix

### Help

The help case launches the real entrypoint with `--help`. It requires exit zero
and a Caret-specific `--provider` option. This catches wrappers that accidentally
route to compiler help or another application.

### Offline Single Shot

The success case loads `mock_claude_cli.sdn`, selects `claude_cli`, supplies a
model and system prompt, and sends `fixture-success`. The configured executable
validates the forwarded arguments and returns deterministic structured JSON.
Caret must print `fixture-ok` and exit zero.

### Provider Error

The error case tells the fixture to exit nonzero after writing an Anthropic-like
secret to stderr. Caret must return exit one, show a redaction marker, and never
expose the original secret. A generic successful response is not accepted.

### Unknown Option

The usage case sends an option that Caret does not implement. It must return
exit two and name the unknown option. This prevents silent argument loss.

### Cached Wrapper Selection

The wrapper case points `SIMPLE_CARET_NATIVE` at a deterministic executable and
requires the original argument vector to reach it unchanged. A second case
points the override at a missing executable and requires exit 127 plus a
specific fail-closed diagnostic. These cases do not claim that a release Caret
artifact was built in the current runtime-blocked lane.

## Exit Contract

| Case | Expected exit | Required output |
|------|--------------:|-----------------|
| Help | 0 | `--provider` |
| Offline single shot | 0 | `fixture-ok` |
| Provider error | 1 | `[REDACTED:` |
| Unknown option | 2 | `unknown option` |
| Explicit cached executable | 0 | forwarded marker |
| Invalid cached override | 127 | `not executable` |

## Frozen Test Interface

`CaretCliFeatureCase` describes one complete process invocation. The process
spec preserves the shared CLI vocabulary:

- `setup_cli_fixture`
- `run_cli_case`
- `check_cli_result`

Displayed flow uses these exact steps:

1. `Load the accepted Claude feature map`
2. `Invoke the caret CLI provider`
3. `Check the structured CLI response`

## Accepted Feature Map

Before any process starts, the scenario reads
`doc/03_plan/trace/llm_caret_claude_cli_full_parity_feature_matrix.tsv` and
requires the CLI capsule row. This is a bounded acceptance witness; it does not
claim that every row in the larger historical Claude parity matrix is complete.

## Fixtures

`test/fixtures/llm_caret/mock_claude_cli.sdn` selects the local executable.
`test/fixtures/llm_caret/mock_claude_cli.shs` validates arguments and emits the
same top-level JSON fields consumed from Claude Code's non-streaming output.
The executable exits immediately when it sees `--max-tokens`, making the removed
flag an observable failure rather than a weak source-text assertion.

## Syntax

Run the interpreter gate:

```bash
bin/simple test test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl --mode=interpreter
```

Run the native gate after the interpreter gate passes:

```bash
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl --mode=native
```

Regenerate this manual:

```bash
bin/simple spipe-docgen test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl --output doc/06_spec --no-index
```

## Failure Handling

The test fails when the entrypoint cannot start, ignores its configured Claude
path, accepts an unknown option, changes documented help, leaks a subprocess
secret, or converts a provider failure into a successful exit.

When failure occurs before the scenario body, inspect the deployed
`bin/simple` runtime for every extern used by `src/app/llm_caret`. A semantic
resolution failure is a runtime/toolchain blocker and must not be reported as a
provider assertion failure. When only the success case fails, run the fixture
directly and compare its accepted arguments with `build_claude_args`.

## Safety

The fixture CLI rejects the removed `--max-tokens` flag and never accesses the
network. No real Claude process or API credential is used.

The test does not read `ANTHROPIC_API_KEY`, does not mutate Claude settings, and
does not resume a real Claude session. Files written by the Simple test runner
remain under its normal build/test evidence directories.

## Evidence Boundary

A passing interpreter and native run proves the Caret process boundary, local
provider dispatch, JSON response path, exit mapping, redaction behavior for the
four provider cases, and cached-wrapper selection/rejection. It complements the
pure CLI feature contract and TUI hidden-feature specification. It does not
replace the full-parity matrix gates, a real release-artifact build, or an
explicitly authorized live-provider run.

## Scenarios

### LLM Caret CLI process hardening

### REQ-LLM-CARET-FULL-003: actual Caret CLI entrypoint

#### should preserve help, success, failure, and usage behavior

- should preserve help, success, failure, and usage behavior
- Load the accepted Claude feature map
   - Expected: cases.len() equals `4`
- Invoke the caret CLI provider
- Check the structured CLI response


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LLM-CARET-FULL-003
# @req REQ-SSPEC-SYSTEM
step("should preserve help, success, failure, and usage behavior")
step("Load the accepted Claude feature map")
expect(file_exists(FEATURE_MAP)).to_be(true)
expect(file_read(FEATURE_MAP)).to_contain("\tcli\t")
expect(file_exists(CONFIG)).to_be(true)

val cases = setup_cli_fixture()
expect(cases.len()).to_equal(4)
for case in cases:
    step("Invoke the caret CLI provider")
    val result = run_cli_case(case)
    step("Check the structured CLI response")
    check_cli_result(case, result)
```

</details>

#### should execute an explicit cached Caret artifact with unchanged arguments

- should execute an explicit cached Caret artifact with unchanged arguments
- Load the accepted Claude feature map
- Invoke the caret CLI provider
- Check the structured CLI response
   - Expected: result.2 equals `0`
   - Expected: result.1 ?? "" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LLM-CARET-FULL-006
# @req REQ-SSPEC-SYSTEM
step("should execute an explicit cached Caret artifact with unchanged arguments")
step("Load the accepted Claude feature map")
expect(file_exists("bin/caret")).to_be(true)
val previous = env_get("SIMPLE_CARET_NATIVE")
expect(env_set("SIMPLE_CARET_NATIVE", "/bin/echo")).to_be(true)

step("Invoke the caret CLI provider")
val result = process_run(
    "bin/caret", ["caret-wrapper-marker", "--plain"]
)
_restore_wrapper_env("SIMPLE_CARET_NATIVE", previous)

step("Check the structured CLI response")
expect(result.2).to_equal(0)
expect(result.0 ?? "").to_contain(
    "caret-wrapper-marker --plain"
)
expect(result.1 ?? "").to_equal("")
```

</details>

#### should reject a missing explicit cached Caret artifact

- should reject a missing explicit cached Caret artifact
- Load the accepted Claude feature map
- Invoke the caret CLI provider
- Check the structured CLI response
   - Expected: result.2 equals `127`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a missing explicit cached Caret artifact")
step("Load the accepted Claude feature map")
val previous = env_get("SIMPLE_CARET_NATIVE")
expect(env_set(
    "SIMPLE_CARET_NATIVE",
    "build/llm_caret/definitely-missing/caret"
)).to_be(true)

step("Invoke the caret CLI provider")
val result = process_run("bin/caret", ["--help"])
_restore_wrapper_env("SIMPLE_CARET_NATIVE", previous)

step("Check the structured CLI response")
expect(result.2).to_equal(127)
expect(result.1 ?? "").to_contain(
    "SIMPLE_CARET_NATIVE is not executable"
)
expect((result.0 ?? "").contains("Usage:")).to_be(false)
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

- **Requirements:** `doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md`
- **Plan:** `doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md`
- **Design:** `doc/05_design/llm_caret_claude_cli_full_parity.md`
- **Research:** `doc/01_research/local/llm_caret_claude_cli_harden.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-FULL-003`
- `REQ-LLM-CARET-FULL-006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a49bccaf530543376577abf6552a8cf67e375095f0994bbcfcfbc42e1171a565`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a49bccaf530543376577abf6552a8cf67e375095f0994bbcfcfbc42e1171a565`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a49bccaf530543376577abf6552a8cf67e375095f0994bbcfcfbc42e1171a565`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl:264:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve help, success, failure, and usage behavior' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl:264:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve help, success, failure, and usage behavior' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl:281:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute an explicit cached Caret artifact with unchanged arguments' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl:281:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should execute an explicit cached Caret artifact with unchanged arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl:303:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a missing explicit cached Caret artifact' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl:303:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a missing explicit cached Caret artifact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
