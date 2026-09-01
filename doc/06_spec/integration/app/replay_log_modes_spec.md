# replay_log_modes_spec

> Purpose: This spec proves replay log mode CLI options.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# replay_log_modes_spec

Purpose: This spec proves replay log mode CLI options.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/replay_log_modes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves replay log mode CLI options.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### replay log mode CLI options

#### shows shared log options in help

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- shows shared log options in help
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-REPLAYLOGMODES-001
step("shows shared log options in help")
val (out, err, code) = _run_replay(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("Usage: simple replay")
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json for missing log file output

- supports log-mode json for missing log file output
- supports log-mode json for missing log file output
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports log-mode json for missing log file output")
step("supports log-mode json for missing log file output")
val (out, err, code) = _run_replay(["--log-mode=json"])
expect(code).to_equal(1)
expect(out).to_contain("\"command\":\"replay\"")
expect(out).to_contain("\"error\":\"replay requires a log file\"")
```

</details>

#### supports dot progress for help output

- supports dot progress for help output
- supports dot progress for help output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports dot progress for help output")
step("supports dot progress for help output")
val (out, err, code) = _run_replay(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("Usage: simple replay")
```

</details>

#### rejects invalid log mode

- rejects invalid log mode
- rejects invalid log mode
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects invalid log mode")
step("rejects invalid log mode")
val (out, err, code) = _run_replay(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### reports a missing build log without spawning another replay process

- reports a missing build log without spawning another replay process
- Ask replay to open a build log that does not exist
- The command returns instead of blocking on a self-spawned child
   - Expected: code equals `1`
- The failure names the missing path and no delegation was attempted


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports a missing build log without spawning another replay process")
"""
An operator types `simple replay build.json` and mistypes the filename.
The command must tell them the file is missing and exit — it must never
hand the same arguments back to another `simple replay` child.

Reproduces doc/08_tracking/bug/
simple_replay_self_spawns_unbounded_process_chain_2026-08-10.md, where
`delegate_replay` re-invoked `./bin/simple replay <same args>`
unconditionally. Each hop stayed alive blocked in wait, so the ~124
processes/min, ~8.4 GB/min chain exhausted a 128 GB host and earlyoom
then killed unrelated healthy `simple` builds.

Two oracles, both required:
  1. the run TERMINATES inside a hard 120 s bound — the defect's parent
     never returned, so a bounded exit is what distinguishes the fixed
     build from the broken one (timeout(1) reports 124);
  2. the reported failure is the non-spawning branch, named by the path
     the user actually typed.
"""
step("Ask replay to open a build log that does not exist")
val (out, err, code) = _run_replay_bounded(["missing-build-log.json"])

step("The command returns instead of blocking on a self-spawned child")
expect(code).to_equal(1)

step("The failure names the missing path and no delegation was attempted")
expect(out + err).to_contain("log file not found: missing-build-log.json")
```

</details>

#### keeps the missing-log failure free of any self-delegation attempt

- keeps the missing-log failure free of any self-delegation attempt
- Run the missing-log case under the same hard time bound
   - Expected: code equals `1`
- No delegated Rust-CLI build-log reader ran
   - Expected: (out + err) does not contain `Failed to read log file`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps the missing-log failure free of any self-delegation attempt")
"""
Prevention oracle for the same defect. A future change that restores a
delegating fallback would either re-enter `simple replay` (the chain) or
shell out to the Rust CLI; both surface as the old build-log wording.
Assert that wording is absent so the guard bites before a fork bomb can
be reproduced on a developer's host.
"""
step("Run the missing-log case under the same hard time bound")
val (out, err, code) = _run_replay_bounded(["missing-build-log.json"])
expect(code).to_equal(1)

step("No delegated Rust-CLI build-log reader ran")
expect(out + err).to_contain("log file not found")
expect((out + err).contains("Failed to read log file")).to_equal(false)
```

</details>

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
- `REQ-REPLAYLOGMODES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `372605aacde45452d4407dfe5c6ba8ac6326f4724734d11dff3857e05b62f43d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `372605aacde45452d4407dfe5c6ba8ac6326f4724734d11dff3857e05b62f43d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `372605aacde45452d4407dfe5c6ba8ac6326f4724734d11dff3857e05b62f43d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/replay_log_modes_spec.spl
mirror: doc/06_spec/integration/app/replay_log_modes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/replay_log_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/replay_log_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/replay_log_modes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/replay_log_modes_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows shared log options in help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/replay_log_modes_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports log-mode json for missing log file output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/replay_log_modes_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports dot progress for help output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
