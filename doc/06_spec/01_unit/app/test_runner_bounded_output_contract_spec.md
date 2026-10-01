# Test Runner Bounded Output Contract Specification

> Tests covering test runner bounded output contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Bounded Output Contract Specification

## Scenarios

### test runner bounded output contract

#### preserves both streams and nonzero status through the limited result wrapper

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves both streams and nonzero status through the limited result wrapper
   - Expected: stdout equals `CHILD_OUT`
   - Expected: stderr equals `CHILD_ERR`
   - Expected: code equals `17`
   - Expected: limited.stdout equals `CHILD_OUT`
   - Expected: limited.stderr equals `CHILD_ERR`
   - Expected: limited.exit_code equals `17`
   - Expected: late.stdout equals `LATE_OUT`
   - Expected: late.stderr equals `LATE_ERR`
   - Expected: late.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("preserves both streams and nonzero status through the limited result wrapper")
val posix_script = "printf CHILD_OUT; printf CHILD_ERR >&2; exit 17"
val windows_script = "<nul set /p \"=CHILD_OUT\" & <nul set /p \"=CHILD_ERR\" 1>&2 & exit /b 17"
val (stdout, stderr, code) = run_bounded_process_case_with_script(
    posix_script, windows_script, 5000, 1024)
val limited = if host_os() == "windows":
    process_run_with_limits_bounded("cmd.exe", ["/D", "/C", windows_script], 5000, 0, 0, 0, 64, 1024)
else:
    process_run_with_limits_bounded("/bin/sh", ["-c", posix_script], 5000, 0, 0, 0, 64, 1024)

expect(stdout).to_equal("CHILD_OUT")
expect(stderr).to_equal("CHILD_ERR")
expect(code).to_equal(17)
expect(limited.stdout).to_equal("CHILD_OUT")
expect(limited.stderr).to_equal("CHILD_ERR")
expect(limited.exit_code).to_equal(17)

if host_os() != "windows":
    val late = process_run_with_limits_bounded(
        "/bin/sh", ["-c", "(sleep 3; printf LATE_OUT; printf LATE_ERR >&2) & exit 0"],
        6000, 0, 0, 0, 64, 1024)
    expect(late.stdout).to_equal("LATE_OUT")
    expect(late.stderr).to_equal("LATE_ERR")
    expect(late.exit_code).to_equal(0)
```

</details>

#### executes the hosted bounded-process ABI instead of a stale missing extern

- executes the hosted bounded-process ABI instead of a stale missing extern
   - Expected: stdout equals ``
   - Expected: code equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("executes the hosted bounded-process ABI instead of a stale missing extern")
val (stdout, stderr, code) = run_bounded_process_case()

expect(stdout).to_equal("")
expect(stderr.len()).to_be_less_than(257)
expect(code).to_equal(-1)
```

</details>

#### preserves and formats a signal status through the bounded-process ABI

- preserves and formats a signal status through the bounded-process ABI
   - Expected: code equals `-1`
   - Expected: "{code}" equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("preserves and formats a signal status through the bounded-process ABI")
if host_os() != "windows":
    val (_, _, code) = process_run_bounded(
        "/bin/sh", ["-c", "kill -ILL $$"], 5000, 256)

    expect(code).to_equal(-1)
    expect("{code}").to_equal("-1")
```

</details>

#### reports every byte omitted when the capture cap is zero

- reports every byte omitted when the capture cap is zero
   - Expected: stdout equals `\n[output truncated: 1 bytes omitted]\n`
   - Expected: stderr equals ``
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports every byte omitted when the capture cap is zero")
val (stdout, stderr, code) = run_bounded_process_case_with_script(
    "printf A", "<nul set /p \"=A\" & exit /b 0", 5000, 0)

expect(stdout).to_equal("\n[output truncated: 1 bytes omitted]\n")
expect(stderr).to_equal("")
expect(code).to_equal(0)
```

</details>

#### uses the single retained byte as head when the capture cap is one

- uses the single retained byte as head when the capture cap is one
   - Expected: stdout equals `A\n[output truncated: 2 bytes omitted]\n`
   - Expected: stderr equals ``
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses the single retained byte as head when the capture cap is one")
val (stdout, stderr, code) = run_bounded_process_case_with_script(
    "printf ABC", "<nul set /p \"=ABC\" & exit /b 0", 5000, 1)

expect(stdout).to_equal("A\n[output truncated: 2 bytes omitted]\n")
expect(stderr).to_equal("")
expect(code).to_equal(0)
```

</details>

#### retains an exact head and tail around the omitted-byte marker

- retains an exact head and tail around the omitted-byte marker
   - Expected: stdout equals `AB\n[output truncated: 4 bytes omitted]\nGH`
   - Expected: stderr equals ``
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("retains an exact head and tail around the omitted-byte marker")
val (stdout, stderr, code) = run_bounded_process_case_with_script(
    "printf ABCDEFGH", "<nul set /p \"=ABCDEFGH\" & exit /b 0", 5000, 4)

expect(stdout).to_equal("AB\n[output truncated: 4 bytes omitted]\nGH")
expect(stderr).to_equal("")
expect(code).to_equal(0)
```

</details>

#### bounds stdout and stderr independently

- bounds stdout and stderr independently
   - Expected: stdout equals `AB\n[output truncated: 5 bytes omitted]\nHI`
   - Expected: stderr equals `12\n[output truncated: 2 bytes omitted]\n56`
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("bounds stdout and stderr independently")
val (stdout, stderr, code) = run_bounded_process_case_with_script(
    "printf ABCDEFGHI; printf 123456 >&2",
    "<nul set /p \"=ABCDEFGHI\" & <nul set /p \"=123456\" 1>&2 & exit /b 0",
    5000, 4)

expect(stdout).to_equal("AB\n[output truncated: 5 bytes omitted]\nHI")
expect(stderr).to_equal("12\n[output truncated: 2 bytes omitted]\n56")
expect(code).to_equal(0)
```

</details>

#### preserves output received before a bounded-process timeout

- preserves output received before a bounded-process timeout
   - Expected: stdout equals `EARLY_OUT`
   - Expected: stderr contains `"TIMEOUT") or stderr`
   - Expected: code equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("preserves output received before a bounded-process timeout")
val timeout_ms = if host_os() == "windows": 1000 else: 250
val (stdout, stderr, code) = run_bounded_process_case_with_script(
    "printf EARLY_OUT; printf EARLY_ERR >&2; sleep 5",
    "<nul set /p \"=EARLY_OUT\" & <nul set /p \"=EARLY_ERR\" 1>&2 & ping -n 6 127.0.0.1 >nul",
    timeout_ms, 64)

expect(stdout).to_equal("EARLY_OUT")
expect(stderr).to_start_with("EARLY_ERR")
expect(stderr.contains("TIMEOUT") or stderr.contains("timed out")).to_equal(true)
expect(code).to_equal(-1)
```

</details>

#### routes daemon and direct child execution through the 4 MiB facade

- routes daemon and direct child execution through the 4 MiB facade


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("routes daemon and direct child execution through the 4 MiB facade")
val single = file_read("src/app/test_runner_new/test_runner_single.spl")
val daemon = file_read("src/app/test_daemon/light_daemon.spl")
val client = file_read("src/app/test_runner_new/test_runner_client.spl")

expect(single).to_contain("process_run_bounded(binary, child_args, timeout_ms, TEST_OUTPUT_CAPTURE_BYTES)")
expect(single).to_contain("stderr.contains(\"TIMEOUT\") or stderr.contains(\"timed out\")")
expect(daemon).to_contain("process_run_bounded(")
expect(daemon).to_contain("TEST_OUTPUT_CAPTURE_BYTES")
expect(daemon).to_contain("\"--timeout\", timeout_secs.to_string()")
expect(client).to_contain("process_run_bounded(")
expect(client).to_contain("TEST_OUTPUT_CAPTURE_BYTES")
```

</details>

#### rejects unbounded process capture in production runner modules

- rejects unbounded process capture in production runner modules
   - Expected: source does not contain `process_run_timeout(`
   - Expected: source does not contain `process_run_with_limits(`
   - Expected: source does not contain `process_run(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects unbounded process capture in production runner modules")
val paths = [
    "src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl",
    "src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl",
    "src/lib/nogc_sync_mut/test_runner/doctest_runner.spl",
    "src/lib/nogc_sync_mut/test_runner/sdoctest/runner.spl",
    "src/lib/nogc_sync_mut/test_runner/test_runner_single.spl",
    "src/lib/nogc_sync_mut/test_runner/process_tracker.spl",
    "src/lib/nogc_sync_mut/test_runner/runner_lifecycle.spl",
]
for path in paths:
    val source = file_read(path)
    expect(source.contains("process_run_timeout(")).to_equal(false)
    expect(source.contains("process_run_with_limits(")).to_equal(false)
    expect(source.contains("process_run(")).to_equal(false)
```

</details>

#### bounds async temp-file reads and the separate fork bridge

- bounds async temp-file reads and the separate fork bridge
   - Expected: async_source does not contain `file_read(run.stdout_file)`
   - Expected: async_source does not contain `file_read(run.stderr_file)`
   - Expected: fork_runtime does not contain `SPL_REALLOC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("bounds async temp-file reads and the separate fork bridge")
val async_source = file_read("src/lib/nogc_sync_mut/test_runner/test_runner_async.spl")
val fork_source = file_read("src/lib/nogc_sync_mut/test_runner/test_runner_fork.spl")
val fork_runtime = file_read("src/runtime/runtime_fork.c")

expect(async_source).to_contain("fn read_bounded_temp_output(path: text) -> Result<text, text>:")
expect(async_source).to_contain("file_read_text_at(path, size - tail_size, tail_size)")
expect(async_source).to_contain('[output truncated: {size - TEST_OUTPUT_CAPTURE_BYTES} bytes omitted]')
expect(async_source.contains("file_read(run.stdout_file)")).to_equal(false)
expect(async_source.contains("file_read(run.stderr_file)")).to_equal(false)
expect(fork_source).to_contain("same 4 MiB-per-stream")
expect(fork_runtime).to_contain("#define FORK_CAPTURE_LIMIT (4U * 1024U * 1024U)")
expect(fork_runtime).to_contain("if (child_exited && timeout_ms <= 0)")
expect(fork_runtime.contains("SPL_REALLOC")).to_equal(false)
```

</details>

#### keeps the legacy APIs while exposing bounded variants

- keeps the legacy APIs while exposing bounded variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the legacy APIs while exposing bounded variants")
val facade = file_read("src/app/io/process_ops.spl")

expect(facade).to_contain("fn process_run(cmd: text, args: [text])")
expect(facade).to_contain("fn process_run_bounded(cmd: text, args: [text], timeout_ms: i64, max_output_bytes: i64)")
expect(facade).to_contain("fn process_run_with_limits(cmd: text, args: [text], timeout_ms: i64, memory_bytes: i64, cpu_seconds: i64, max_fds: i64, max_procs: i64)")
expect(facade).to_contain("fn process_run_with_limits_bounded(cmd: text, args: [text], timeout_ms: i64, memory_bytes: i64, cpu_seconds: i64, max_fds: i64, max_procs: i64, max_output_bytes: i64)")
```

</details>

#### execs the timeout wrapper instead of leaving an extra shell child

- execs the timeout wrapper instead of leaving an extra shell child


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("execs the timeout wrapper instead of leaving an extra shell child")
val app_facade = file_read("src/app/io/process_ops.spl")
val lib_facade = file_read("src/lib/nogc_sync_mut/io/process_ops.spl")

expect(app_facade).to_contain('val redirected_cmd = "exec {cmd_line}')
expect(lib_facade).to_contain('val redirected_cmd = "exec {command_line}')
```

</details>

#### requires timeout evidence before classifying exit minus one

- requires timeout evidence before classifying exit minus one


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("requires timeout evidence before classifying exit minus one")
val parser = file_read("src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl")
val sdoctest = file_read("src/lib/nogc_sync_mut/test_runner/sdoctest/runner.spl")
val doctest = file_read("src/lib/nogc_sync_mut/test_runner/doctest_runner.spl")
val app_facade = file_read("src/app/io/process_ops.spl")
val lib_facade = file_read("src/lib/nogc_sync_mut/io/process_ops.spl")
val marker_guard = 'exit_code == -1 and (stderr.contains("TIMEOUT") or stderr.contains("timed out"))'
val timeout_evidence = 'stderr.contains("TIMEOUT") or stderr.contains("timed out")'
val limit_guard = 'code == -1 and (stderr.contains("TIMEOUT") or stderr.contains("timed out"))'

expect(parser).to_contain(marker_guard)
expect(sdoctest).to_contain("if exit_code == -1:")
expect(sdoctest).to_contain(timeout_evidence)
expect(sdoctest).to_contain("Process failed to start or returned an internal error")
expect(doctest).to_contain("if exit_code == -1:")
expect(doctest).to_contain(timeout_evidence)
expect(doctest).to_contain("Process failed to start or returned an internal error")
expect(app_facade).to_contain(limit_guard)
expect(lib_facade).to_contain(limit_guard)
expect(app_facade).to_contain('limit_type = "timeout"')
expect(lib_facade).to_contain('limit_type = "timeout"')
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_bounded_output_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering test runner bounded output contract.
- test runner bounded output contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `2f7b5157507935b8799deb836936a9bea073f060cebb3d5ef9ae6dbc231aa682`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2f7b5157507935b8799deb836936a9bea073f060cebb3d5ef9ae6dbc231aa682`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2f7b5157507935b8799deb836936a9bea073f060cebb3d5ef9ae6dbc231aa682`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **70/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/test_runner_bounded_output_contract_spec.spl
mirror: doc/06_spec/01_unit/app/test_runner_bounded_output_contract_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=20
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=70; blocker cap makes effective=49
doc/06_spec/01_unit/app/test_runner_bounded_output_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/test_runner_bounded_output_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/test_runner_bounded_output_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/test_runner_bounded_output_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/test_runner_bounded_output_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/test_runner_bounded_output_contract_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves both streams and nonzero status through the limited result wrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_bounded_output_contract_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes the hosted bounded-process ABI instead of a stale missing extern' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_bounded_output_contract_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves and formats a signal status through the bounded-process ABI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
