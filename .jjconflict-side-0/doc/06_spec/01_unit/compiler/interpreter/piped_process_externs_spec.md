# Piped-process externs must be reachable from the interpreter

> Guards doc/08_tracking/bug/interpreter_sffi_missing_piped_process_externs_2026-07-29.md

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Piped-process externs must be reachable from the interpreter

Guards doc/08_tracking/bug/interpreter_sffi_missing_piped_process_externs_2026-07-29.md

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/piped_process_externs_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Guards doc/08_tracking/bug/interpreter_sffi_missing_piped_process_externs_2026-07-29.md

`rt_process_spawn_piped` / `rt_process_write_stdin` / `rt_process_read_stdout` /
`rt_process_is_alive` / `rt_process_close_piped` have existed in the C runtime
(`src/runtime/runtime_process.c`) for a long time and are declared `extern fn`
by shipping Simple code (`src/app/editor/debug_process_runtime.spl`), but none
of the five was ever registered in the interpreter's extern dispatch table
(`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`). Any interpreted
program touching them died at semantic analysis:

    error: semantic: unknown extern function: rt_process_spawn_piped

WHY A SUBPROCESS. An unregistered extern is rejected at semantic analysis, which
kills the ENTIRE file before a single example runs. Calling these externs from a
spec body directly would therefore not produce a failing example -- it would
produce a zero-example file, which reads as a pass. The oracle is instead the
sibling run-path probe executed as a subprocess, whose verdict line is present
only when every extern resolved AND every behavioural check passed.

## Scenarios

### piped-process externs under the interpreter

#### resolves rt_process_spawn_piped instead of failing semantic analysis

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves rt_process_spawn_piped instead of failing semantic analysis
- Run the piped-process probe under SIMPLE_EXECUTION_MODE=interpret
- The exact pre-fix symptom must be gone -- this is the reproducing assertion
- Non-vacuity: the probe must actually have reached its first check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves rt_process_spawn_piped instead of failing semantic analysis")
step("Run the piped-process probe under SIMPLE_EXECUTION_MODE=interpret")
val out = run_probe(REPRO_PROBE)

step("The exact pre-fix symptom must be gone -- this is the reproducing assertion")
expect(out).to_not_contain("unknown extern function")

step("Non-vacuity: the probe must actually have reached its first check")
expect(out).to_contain("PASS spawn_piped_returns_real_pid")
```

</details>

#### round-trips real bytes through the child's stdin and stdout

- round-trips real bytes through the child's stdin and stdout
- Run the probe again and read its behavioural checks
- stdin write and non-blocking stdout read must move the exact payload
- A registered-but-stubbed extern would pass the resolution check and fail here


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips real bytes through the child's stdin and stdout")
step("Run the probe again and read its behavioural checks")
val out = run_probe(REPRO_PROBE)

step("stdin write and non-blocking stdout read must move the exact payload")
expect(out).to_contain("PASS write_stdin_succeeds")
expect(out).to_contain("PASS read_stdout_returns_exactly_what_was_written")

step("A registered-but-stubbed extern would pass the resolution check and fail here")
expect(out).to_contain("PASS is_alive_true_for_fresh_child")
expect(out).to_contain("PASS close_piped_succeeds")
expect(out).to_contain("PASS is_alive_false_after_close")
```

</details>

#### reports an unambiguous all-pass verdict

- reports an unambiguous all-pass verdict
- The verdict line is printed only when zero checks failed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports an unambiguous all-pass verdict")
step("The verdict line is printed only when zero checks failed")
val out = run_probe(REPRO_PROBE)
expect(out).to_contain("PIPED PROCESS PROBE: ALL PASS")
expect(out).to_not_contain("FAILURES")
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9744ae1c287b1bfee231979ccf129e4cecce88e0f52d34314223d682dbc89679`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9744ae1c287b1bfee231979ccf129e4cecce88e0f52d34314223d682dbc89679`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9744ae1c287b1bfee231979ccf129e4cecce88e0f52d34314223d682dbc89679`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interpreter/piped_process_externs_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/piped_process_externs_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/piped_process_externs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/piped_process_externs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/piped_process_externs_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves rt_process_spawn_piped instead of failing semantic analysis' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/piped_process_externs_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips real bytes through the child's stdin and stdout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/piped_process_externs_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports an unambiguous all-pass verdict' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
