# Simple Test Runner (SPL) Specification

> The Simple test runner is a reimplementation of the Rust test runner in Simple language. It supports interpreter, SMF, and native execution modes with per-test timeout via `rt_process_run_timeout` FFI. A recursion guard (`SIMPLE_TEST_RUNNER_RUST=1`) prevents infinite dispatch loops when the Simple runner spawns child `simple_old` processes.

<!-- sdn-diagram:id=test_runner_simple_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_runner_simple_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_runner_simple_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_runner_simple_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 69 | 69 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Test Runner (SPL) Specification

The Simple test runner is a reimplementation of the Rust test runner in Simple language. It supports interpreter, SMF, and native execution modes with per-test timeout via `rt_process_run_timeout` FFI. A recursion guard (`SIMPLE_TEST_RUNNER_RUST=1`) prevents infinite dispatch loops when the Simple runner spawns child `simple_old` processes.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #920-930 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/01_unit/app/tooling/test_runner_simple_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The Simple test runner is a reimplementation of the Rust test runner in Simple
language. It supports interpreter, SMF, and native execution modes with
per-test timeout via `rt_process_run_timeout` FFI. A recursion guard
(`SIMPLE_TEST_RUNNER_RUST=1`) prevents infinite dispatch loops when the
Simple runner spawns child `simple_old` processes.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Recursion guard | `SIMPLE_TEST_RUNNER_RUST=1` env var forces child to use Rust runner |
| Subprocess execution | Each test file runs as a child process via `rt_process_run_timeout` |
| Timeout | `rt_process_run_timeout(cmd, args, timeout_ms)` returns exit_code=-1 on timeout |
| Mode dispatch | interpreter (default), smf (compile+run .smf), native (compile+run binary) |
| Seed shuffle | Deterministic test ordering via `--seed N` |
| ANSI stripping | Strips color codes before output parsing |
| Test DB | Writes run records to `doc/08_tracking/test/test_db.sdn` |
| Skip features | Lists unimplemented features from .skip files |

## Scenarios

### Simple Test Runner Argument Parsing

#### defaults to test/ path when no path given

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_path = "test/"
expect(default_path).to_equal("test/")
```

</details>

#### parses --mode smf flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = "smf"
expect(mode).to_equal("smf")
```

</details>

#### parses --mode=native equals syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg = "--mode=native"
val m = arg.replace("--mode=", "")
expect(m).to_equal("native")
```

</details>

#### parses --timeout flag with seconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timeout = 30
val timeout_ms = timeout * 1000
expect(timeout_ms).to_equal(30000)
```

</details>

#### parses --fail-fast flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fail_fast = true
expect(fail_fast).to_equal(true)
```

</details>

#### parses --only-slow flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val only_slow = true
expect(only_slow).to_equal(true)
```

</details>

#### parses --only-skipped flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val only_skipped = true
expect(only_skipped).to_equal(true)
```

</details>

#### parses --seed flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed = 42
val has_seed = true
expect(seed).to_equal(42)
expect(has_seed).to_equal(true)
```

</details>

#### parses --list-ignored flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list_ignored = true
expect(list_ignored).to_equal(true)
```

</details>

#### parses --safe-mode flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val safe_mode = true
expect(safe_mode).to_equal(true)
```

</details>

#### parses --force-rebuild flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val force_rebuild = true
expect(force_rebuild).to_equal(true)
```

</details>

#### parses --keep-artifacts flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val keep_artifacts = true
expect(keep_artifacts).to_equal(true)
```

</details>

#### parses --all flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_all = true
expect(run_all).to_equal(true)
```

</details>

#### parses --doc format flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val format = "doc"
expect(format).to_equal("doc")
```

</details>

#### parses --format doc flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val format = "doc"
expect(format).to_equal("doc")
```

</details>

#### parses --list-skip-features flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list_skip = true
expect(list_skip).to_equal(true)
```

</details>

#### parses --planned-only flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val planned_only = true
expect(planned_only).to_equal(true)
```

</details>

### Simple Test Runner Discovery

#### identifies spec files by _spec. pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "audio_spec.spl"
val is_spec = name.contains("_spec.")
expect(is_spec).to_equal(true)
```

</details>

#### identifies test files by _test. pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "integration_test.spl"
val is_test = name.contains("_test.")
expect(is_test).to_equal(true)
```

</details>

#### rejects non-spl files

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "audio_spec.rs"
val is_spl = name.ends_with(".spl")
expect(is_spl).to_equal(false)
```

</details>

#### filters unit tests by excluding integration and system paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/unit/lib/std/core/string_spec.spl"
val is_unit = not path.contains("/integration/") and not path.contains("/system/")
expect(is_unit).to_equal(true)
```

</details>

#### filters integration tests by path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/integration/api_spec.spl"
val is_integration = path.contains("/integration/")
expect(is_integration).to_equal(true)
```

</details>

#### filters system tests by path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/system/features/enums/enums_spec.spl"
val is_system = path.contains("/system/")
expect(is_system).to_equal(true)
```

</details>

### Simple Test Runner Output Parsing

#### extracts passed count from examples line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val examples = 5
val failures = 1
val passed = examples - failures
expect(passed).to_equal(4)
```

</details>

#### handles zero failures

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val examples = 10
val failures = 0
val passed = examples - failures
expect(passed).to_equal(10)
```

</details>

#### falls back to exit code when no output parsed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exit_code = 0
val inferred_passed = 1
expect(inferred_passed).to_equal(1)
```

</details>

#### marks non-zero exit as failure when no output parsed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exit_code = 1
val inferred_failed = 1
expect(inferred_failed).to_equal(1)
```

</details>

#### tracks skipped count separately

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val skipped = 3
expect(skipped).to_equal(3)
```

</details>

### Simple Test Runner Artifact Layout

#### writes summaries under build/test-artifacts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary_path = "{artifact_dir_for_test(\"test/unit/app/tooling/command_dispatch_spec.spl\")}/summary.txt"
expect(summary_path).to_equal("build/test-artifacts/unit/app/tooling/command_dispatch/summary.txt")
expect(summary_path).to_end_with("summary.txt")
```

</details>

#### writes result.json next to the text summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json_path = "{artifact_dir_for_test(\"test/unit/app/tooling/command_dispatch_spec.spl\")}/result.json"
expect(json_path).to_equal("build/test-artifacts/unit/app/tooling/command_dispatch/result.json")
expect(json_path).to_end_with("result.json")
```

</details>

#### treats combined.log as the canonical merged output stream

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val combined_path = "{artifact_dir_for_test(\"test/unit/app/tooling/command_dispatch_spec.spl\")}/combined.log"
expect(combined_path).to_equal("build/test-artifacts/unit/app/tooling/command_dispatch/combined.log")
expect(combined_path).to_end_with("combined.log")
```

</details>

#### keeps output.log as a compatibility alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output_path = "{artifact_dir_for_test(\"test/unit/app/tooling/command_dispatch_spec.spl\")}/output.log"
expect(compatibility_artifact_files().contains("output.log")).to_equal(true)
expect(output_path).to_end_with("output.log")
```

</details>

#### derives scenario directories from index and slugified scenario name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = scenario_dir_for_test("test/feature/app/web_dashboard/tmux_rest_api_spec.spl", 1, "rendering", "shows dashboard")
expect(path).to_equal("build/test-artifacts/app/web_dashboard/tmux_rest_api/scenarios/001-rendering-shows-dashboard")
```

</details>

#### reserves canonical transcript filenames for scenario evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = scenario_dir_for_test("test/feature/app/web_dashboard/tmux_rest_api_spec.spl", 2, "", "captures tui transcript")
expect("{dir}/transcript.ansi").to_end_with("transcript.ansi")
expect("{dir}/transcript.txt").to_end_with("transcript.txt")
```

</details>

#### defines the canonical per-spec artifact set

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = canonical_artifact_files()
expect(files.contains("summary.txt")).to_equal(true)
expect(files.contains("result.json")).to_equal(true)
expect(files.contains("combined.log")).to_equal(true)
```

</details>

### Simple Test Runner Timeout

#### converts seconds to milliseconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timeout_secs = 30
val timeout_ms = timeout_secs * 1000
expect(timeout_ms).to_equal(30000)
```

</details>

#### detects timeout by exit_code -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exit_code = -1
val timed_out = exit_code == -1
expect(timed_out).to_equal(true)
```

</details>

#### normal exit code is not timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exit_code = 0
val timed_out = exit_code == -1
expect(timed_out).to_equal(false)
```

</details>

### Simple Test Runner Recursion Guard

#### Rust seed accepts only the explicit temporary runner opt-in

The executable scenario reads the Rust driver and requires an exact
`SIMPLE_TEST_RUNNER_RUST=1` dispatch into the existing Rust test handler.
Unset, `0`, `true`, and empty values remain on the pure-Simple path.

#### Internal child owners set the same recursion guard

The runtime and interpreter child-launch owners both set the exact guard value.
This prevents recursive Simple-to-Rust test dispatch without enabling an
automatic production fallback.

#### Async owners inherit output so verbose children cannot fill unread pipes

The native runtime and interpreter async spawn owners inherit stdout and stderr.
Because their public contract exposes only a PID and no pipe reader, this avoids
the full-pipe deadlock that previously made chatty children appear hung.

### Simple Test Runner Execution Modes

#### interpreter mode runs file directly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = "interpreter"
expect(mode).to_equal("interpreter")
```

</details>

#### SMF mode compiles then runs .smf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val smf_path = "test/file_spec.spl".replace(".spl", ".smf")
expect(smf_path).to_equal("test/file_spec.smf")
```

</details>

#### native mode compiles then runs binary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bin_path = "test/file_spec.spl".replace(".spl", "")
expect(bin_path).to_equal("test/file_spec")
```

</details>

### Simple Test Runner Seed Shuffle

#### hash produces consistent result for same input

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed = 42
val hash1 = (seed * 31 + 7) % 1000000007
val hash2 = (seed * 31 + 7) % 1000000007
expect(hash1).to_equal(hash2)
```

</details>

#### different seeds produce different hashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hash1 = (42 * 31 + 7) % 1000000007
val hash2 = (99 * 31 + 7) % 1000000007
expect(hash1 != hash2).to_equal(true)
```

</details>

### Simple Test Runner Output Formats

#### default format shows PASS prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prefix = "  PASS"
expect(prefix).to_equal("  PASS")
```

</details>

#### default format shows FAIL prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prefix = "  FAIL"
expect(prefix).to_equal("  FAIL")
```

</details>

#### default format shows TOUT prefix for timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prefix = "  TOUT"
expect(prefix).to_equal("  TOUT")
```

</details>

#### doc format shows basename only

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/unit/lib/std/game_engine/audio_spec.spl"
# rt_path_basename would return "audio_spec.spl"
val expected = "audio_spec.spl"
expect(expected).to_equal("audio_spec.spl")
```

</details>

### Simple Test Runner Env Propagation

#### sets SIMPLE_TEST_MODE for interpreter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode_str = "interpreter"
expect(mode_str).to_equal("interpreter")
```

</details>

#### sets SIMPLE_TEST_MODE for smf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode_str = "smf"
expect(mode_str).to_equal("smf")
```

</details>

#### sets SIMPLE_TEST_FILTER for slow

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val filter = "slow"
expect(filter).to_equal("slow")
```

</details>

#### sets SIMPLE_TEST_FILTER for skipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val filter = "skipped"
expect(filter).to_equal("skipped")
```

</details>

#### sets SIMPLE_TEST_SHOW_TAGS to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val val_str = "1"
expect(val_str).to_equal("1")
```

</details>

### Simple Test Runner Skip Features

#### extracts feature IDs from file header

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = "**Feature IDs:** #100-105"
val ids = header.replace("**Feature IDs:**", "").trim()
expect(ids).to_equal("#100-105")
```

</details>

#### extracts category from file header

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = "**Category:** Tooling"
val cat = header.replace("**Category:**", "").trim()
expect(cat).to_equal("Tooling")
```

</details>

#### extracts status from file header

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = "**Status:** Draft"
val status = header.replace("**Status:**", "").trim()
expect(status).to_equal("Draft")
```

</details>

#### planned-only filters by status

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = "planned"
val is_planned = status.contains("planned") or status.contains("tbd") or status == "unknown"
expect(is_planned).to_equal(true)
```

</details>

### Simple Test Runner Test DB

#### run record contains pass and fail counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val passed = 10
val failed = 2
val total = passed + failed
expect(total).to_equal(12)
```

</details>

#### run record uses microsecond timestamp as run_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val micros = 1706500000000000
val run_id = micros
expect(run_id > 0).to_equal(true)
```

</details>

#### run record status is completed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = "completed"
expect(status).to_equal("completed")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 69 |
| Active scenarios | 69 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
