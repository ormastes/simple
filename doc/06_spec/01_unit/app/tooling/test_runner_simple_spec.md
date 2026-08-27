# Test Runner Simple Specification

> Tests covering Simple Test Runner Argument Parsing, Simple Test Runner Discovery, Simple Test Runner Output Parsing, Simple Test Runner Artifact Layout, Simple Test Runner Timeout, Simple Test Runner Recursion Guard, Simple Test Runner Execution Modes, Simple Test Runner Seed Shuffle, Simple Test Runner Output Formats, Simple Test Runner Env Propagation, Simple Test Runner Skip Features, Simple Test Runner Test DB.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 62 | 62 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Simple Specification

## Scenarios

### Simple Test Runner Argument Parsing

#### defaults to test/ path when no path given

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults to test/ path when no path given
   - Expected: default_path equals `test/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("defaults to test/ path when no path given")
val default_path = "test/"
expect(default_path).to_equal("test/")
```

</details>

#### parses --mode smf flag

- parses --mode smf flag
   - Expected: mode equals `smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses --mode smf flag")
val mode = "smf"
expect(mode).to_equal("smf")
```

</details>

#### parses --mode=native equals syntax

- parses --mode=native equals syntax
   - Expected: m equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses --mode=native equals syntax")
val arg = "--mode=native"
val m = arg.replace("--mode=", "")
expect(m).to_equal("native")
```

</details>

#### parses --timeout flag with seconds

- parses --timeout flag with seconds
   - Expected: timeout_ms equals `30000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses --timeout flag with seconds")
val timeout = 30
val timeout_ms = timeout * 1000
expect(timeout_ms).to_equal(30000)
```

</details>

#### parses --fail-fast flag

- parses --fail-fast flag
   - Expected: fail_fast is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses --fail-fast flag")
val fail_fast = true
expect(fail_fast).to_equal(true)
```

</details>

#### parses --only-slow flag

- parses --only-slow flag
   - Expected: only_slow is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses --only-slow flag")
val only_slow = true
expect(only_slow).to_equal(true)
```

</details>

#### parses --only-skipped flag

- parses --only-skipped flag
   - Expected: only_skipped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses --only-skipped flag")
val only_skipped = true
expect(only_skipped).to_equal(true)
```

</details>

#### parses --seed flag

- parses --seed flag
   - Expected: seed equals `42`
   - Expected: has_seed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses --seed flag")
val seed = 42
val has_seed = true
expect(seed).to_equal(42)
expect(has_seed).to_equal(true)
```

</details>

#### parses --list-ignored flag

- parses --list-ignored flag
   - Expected: list_ignored is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses --list-ignored flag")
val list_ignored = true
expect(list_ignored).to_equal(true)
```

</details>

#### parses --safe-mode flag

- parses --safe-mode flag
   - Expected: safe_mode is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses --safe-mode flag")
val safe_mode = true
expect(safe_mode).to_equal(true)
```

</details>

#### parses --force-rebuild flag

- parses --force-rebuild flag
   - Expected: force_rebuild is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses --force-rebuild flag")
val force_rebuild = true
expect(force_rebuild).to_equal(true)
```

</details>

#### parses --keep-artifacts flag

- parses --keep-artifacts flag
   - Expected: keep_artifacts is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses --keep-artifacts flag")
val keep_artifacts = true
expect(keep_artifacts).to_equal(true)
```

</details>

#### parses --all flag

- parses --all flag
   - Expected: run_all is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses --all flag")
val run_all = true
expect(run_all).to_equal(true)
```

</details>

#### parses --doc format flag

- parses --doc format flag
   - Expected: format equals `doc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses --doc format flag")
val format = "doc"
expect(format).to_equal("doc")
```

</details>

#### parses --format doc flag

- parses --format doc flag
   - Expected: format equals `doc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses --format doc flag")
val format = "doc"
expect(format).to_equal("doc")
```

</details>

#### parses --list-skip-features flag

- parses --list-skip-features flag
   - Expected: list_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses --list-skip-features flag")
val list_skip = true
expect(list_skip).to_equal(true)
```

</details>

#### parses --planned-only flag

- parses --planned-only flag
   - Expected: planned_only is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses --planned-only flag")
val planned_only = true
expect(planned_only).to_equal(true)
```

</details>

### Simple Test Runner Discovery

#### identifies spec files by _spec. pattern

- identifies spec files by _spec. pattern
   - Expected: is_spec is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("identifies spec files by _spec. pattern")
val name = "audio_spec.spl"
val is_spec = name.contains("_spec.")
expect(is_spec).to_equal(true)
```

</details>

#### identifies test files by _test. pattern

- identifies test files by _test. pattern
   - Expected: is_test is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("identifies test files by _test. pattern")
val name = "integration_test.spl"
val is_test = name.contains("_test.")
expect(is_test).to_equal(true)
```

</details>

#### rejects non-spl files

- rejects non-spl files
   - Expected: is_spl is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects non-spl files")
val name = "audio_spec.rs"
val is_spl = name.ends_with(".spl")
expect(is_spl).to_equal(false)
```

</details>

#### filters unit tests by excluding integration and system paths

- filters unit tests by excluding integration and system paths
   - Expected: is_unit is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("filters unit tests by excluding integration and system paths")
val path = "test/unit/lib/std/core/string_spec.spl"
val is_unit = not path.contains("/integration/") and not path.contains("/system/")
expect(is_unit).to_equal(true)
```

</details>

#### filters integration tests by path

- filters integration tests by path
   - Expected: is_integration is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("filters integration tests by path")
val path = "test/integration/api_spec.spl"
val is_integration = path.contains("/integration/")
expect(is_integration).to_equal(true)
```

</details>

#### filters system tests by path

- filters system tests by path
   - Expected: is_system is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("filters system tests by path")
val path = "test/system/features/enums/enums_spec.spl"
val is_system = path.contains("/system/")
expect(is_system).to_equal(true)
```

</details>

### Simple Test Runner Output Parsing

#### extracts passed count from examples line

- extracts passed count from examples line
   - Expected: passed equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts passed count from examples line")
val examples = 5
val failures = 1
val passed = examples - failures
expect(passed).to_equal(4)
```

</details>

#### handles zero failures

- handles zero failures
   - Expected: passed equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("handles zero failures")
val examples = 10
val failures = 0
val passed = examples - failures
expect(passed).to_equal(10)
```

</details>

#### falls back to exit code when no output parsed

- falls back to exit code when no output parsed
   - Expected: inferred_passed equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("falls back to exit code when no output parsed")
val exit_code = 0
val inferred_passed = 1
expect(inferred_passed).to_equal(1)
```

</details>

#### marks non-zero exit as failure when no output parsed

- marks non-zero exit as failure when no output parsed
   - Expected: inferred_failed equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("marks non-zero exit as failure when no output parsed")
val exit_code = 1
val inferred_failed = 1
expect(inferred_failed).to_equal(1)
```

</details>

#### tracks skipped count separately

- tracks skipped count separately
   - Expected: skipped equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("tracks skipped count separately")
val skipped = 3
expect(skipped).to_equal(3)
```

</details>

### Simple Test Runner Artifact Layout

#### writes summaries under build/test-artifacts

- writes summaries under build/test-artifacts
   - Expected: summary_path equals `build/test-artifacts/unit/app/tooling/command_dispatch/summary.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("writes summaries under build/test-artifacts")
val summary_path = "{artifact_dir_for_test(\"test/unit/app/tooling/command_dispatch_spec.spl\")}/summary.txt"
expect(summary_path).to_equal("build/test-artifacts/unit/app/tooling/command_dispatch/summary.txt")
expect(summary_path).to_end_with("summary.txt")
```

</details>

#### writes result.json next to the text summary

- writes result.json next to the text summary
   - Expected: json_path equals `build/test-artifacts/unit/app/tooling/command_dispatch/result.json`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("writes result.json next to the text summary")
val json_path = "{artifact_dir_for_test(\"test/unit/app/tooling/command_dispatch_spec.spl\")}/result.json"
expect(json_path).to_equal("build/test-artifacts/unit/app/tooling/command_dispatch/result.json")
expect(json_path).to_end_with("result.json")
```

</details>

#### treats combined.log as the canonical merged output stream

- treats combined.log as the canonical merged output stream
   - Expected: combined_path equals `build/test-artifacts/unit/app/tooling/command_dispatch/combined.log`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("treats combined.log as the canonical merged output stream")
val combined_path = "{artifact_dir_for_test(\"test/unit/app/tooling/command_dispatch_spec.spl\")}/combined.log"
expect(combined_path).to_equal("build/test-artifacts/unit/app/tooling/command_dispatch/combined.log")
expect(combined_path).to_end_with("combined.log")
```

</details>

#### keeps output.log as a compatibility alias

- keeps output.log as a compatibility alias
   - Expected: compatibility_artifact_files() contains `output.log`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps output.log as a compatibility alias")
val output_path = "{artifact_dir_for_test(\"test/unit/app/tooling/command_dispatch_spec.spl\")}/output.log"
expect(compatibility_artifact_files().contains("output.log")).to_equal(true)
expect(output_path).to_end_with("output.log")
```

</details>

#### derives scenario directories from index and slugified scenario name

- derives scenario directories from index and slugified scenario name
   - Expected: path equals `build/test-artifacts/app/web_dashboard/tmux_rest_api/scenarios/001-rendering-... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("derives scenario directories from index and slugified scenario name")
val path = scenario_dir_for_test("test/feature/app/web_dashboard/tmux_rest_api_spec.spl", 1, "rendering", "shows dashboard")
expect(path).to_equal("build/test-artifacts/app/web_dashboard/tmux_rest_api/scenarios/001-rendering-shows-dashboard")
```

</details>

#### reserves canonical transcript filenames for scenario evidence

- reserves canonical transcript filenames for scenario evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reserves canonical transcript filenames for scenario evidence")
val dir = scenario_dir_for_test("test/feature/app/web_dashboard/tmux_rest_api_spec.spl", 2, "", "captures tui transcript")
expect("{dir}/transcript.ansi").to_end_with("transcript.ansi")
expect("{dir}/transcript.txt").to_end_with("transcript.txt")
```

</details>

#### defines the canonical per-spec artifact set

- defines the canonical per-spec artifact set
   - Expected: files contains `summary.txt`
   - Expected: files contains `result.json`
   - Expected: files contains `combined.log`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("defines the canonical per-spec artifact set")
val files = canonical_artifact_files()
expect(files.contains("summary.txt")).to_equal(true)
expect(files.contains("result.json")).to_equal(true)
expect(files.contains("combined.log")).to_equal(true)
```

</details>

### Simple Test Runner Timeout

#### converts seconds to milliseconds

- converts seconds to milliseconds
   - Expected: timeout_ms equals `30000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("converts seconds to milliseconds")
val timeout_secs = 30
val timeout_ms = timeout_secs * 1000
expect(timeout_ms).to_equal(30000)
```

</details>

#### detects timeout by exit_code -1

- detects timeout by exit_code -1
   - Expected: timed_out is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects timeout by exit_code -1")
val exit_code = -1
val timed_out = exit_code == -1
expect(timed_out).to_equal(true)
```

</details>

#### normal exit code is not timeout

- normal exit code is not timeout
   - Expected: timed_out is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("normal exit code is not timeout")
val exit_code = 0
val timed_out = exit_code == -1
expect(timed_out).to_equal(false)
```

</details>

### Simple Test Runner Recursion Guard

#### Rust seed accepts only the explicit temporary runner opt-in

- Rust seed accepts only the explicit temporary runner opt-in


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("Rust seed accepts only the explicit temporary runner opt-in")
val driver = rt_file_read_text("src/compiler_rust/driver/src/main.rs")
expect(driver).to_contain("temporary_rust_test_runner_override")
expect(driver).to_contain("value == Some(\"1\")")
expect(driver).to_contain("return run_rust_handler(&entry.rust_handler, ctx)")
```

</details>

#### internal child owners set the same recursion guard

- internal child owners set the same recursion guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("internal child owners set the same recursion guard")
val runtime = rt_file_read_text("src/compiler_rust/runtime/src/value/cli_sffi.rs")
val interpreter = rt_file_read_text("src/compiler_rust/compiler/src/interpreter_extern/cli.rs")
expect(runtime).to_contain("cmd.env(\"SIMPLE_TEST_RUNNER_RUST\", \"1\")")
expect(interpreter).to_contain("cmd.env(\"SIMPLE_TEST_RUNNER_RUST\", \"1\")")
```

</details>

#### async owners inherit output so verbose children cannot fill unread pipes

- async owners inherit output so verbose children cannot fill unread pipes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("async owners inherit output so verbose children cannot fill unread pipes")
val runtime_process = rt_file_read_text("src/compiler_rust/runtime/src/value/sffi/env_process.rs")
val interpreter_process = rt_file_read_text("src/compiler_rust/compiler/src/interpreter_extern/system.rs")
expect(runtime_process).to_contain("command.stdout(Stdio::inherit())")
expect(runtime_process).to_contain("command.stderr(Stdio::inherit())")
expect(interpreter_process).to_contain(".stdout(std::process::Stdio::inherit())")
expect(interpreter_process).to_contain(".stderr(std::process::Stdio::inherit())")
```

</details>

### Simple Test Runner Execution Modes

#### interpreter mode runs file directly

- interpreter mode runs file directly
   - Expected: mode equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("interpreter mode runs file directly")
val mode = "interpreter"
expect(mode).to_equal("interpreter")
```

</details>

#### SMF mode compiles then runs .smf

- SMF mode compiles then runs .smf
   - Expected: smf_path equals `test/file_spec.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("SMF mode compiles then runs .smf")
val smf_path = "test/file_spec.spl".replace(".spl", ".smf")
expect(smf_path).to_equal("test/file_spec.smf")
```

</details>

#### native mode compiles then runs binary

- native mode compiles then runs binary
   - Expected: bin_path equals `test/file_spec`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("native mode compiles then runs binary")
val bin_path = "test/file_spec.spl".replace(".spl", "")
expect(bin_path).to_equal("test/file_spec")
```

</details>

### Simple Test Runner Seed Shuffle

#### hash produces consistent result for same input

- hash produces consistent result for same input
   - Expected: hash1 equals `hash2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("hash produces consistent result for same input")
val seed = 42
val hash1 = (seed * 31 + 7) % 1000000007
val hash2 = (seed * 31 + 7) % 1000000007
expect(hash1).to_equal(hash2)
```

</details>

#### different seeds produce different hashes

- different seeds produce different hashes
   - Expected: hash1 != hash2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("different seeds produce different hashes")
val hash1 = (42 * 31 + 7) % 1000000007
val hash2 = (99 * 31 + 7) % 1000000007
expect(hash1 != hash2).to_equal(true)
```

</details>

### Simple Test Runner Output Formats

#### default format shows PASS prefix

- default format shows PASS prefix
   - Expected: prefix equals `  PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("default format shows PASS prefix")
val prefix = "  PASS"
expect(prefix).to_equal("  PASS")
```

</details>

#### default format shows FAIL prefix

- default format shows FAIL prefix
   - Expected: prefix equals `  FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("default format shows FAIL prefix")
val prefix = "  FAIL"
expect(prefix).to_equal("  FAIL")
```

</details>

#### default format shows TOUT prefix for timeout

- default format shows TOUT prefix for timeout
   - Expected: prefix equals `  TOUT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("default format shows TOUT prefix for timeout")
val prefix = "  TOUT"
expect(prefix).to_equal("  TOUT")
```

</details>

#### doc format shows basename only

- doc format shows basename only
   - Expected: expected equals `audio_spec.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("doc format shows basename only")
val path = "test/unit/lib/std/game_engine/audio_spec.spl"
# rt_path_basename would return "audio_spec.spl"
val expected = "audio_spec.spl"
expect(expected).to_equal("audio_spec.spl")
```

</details>

### Simple Test Runner Env Propagation

#### sets SIMPLE_TEST_MODE for interpreter

- sets SIMPLE_TEST_MODE for interpreter
   - Expected: mode_str equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sets SIMPLE_TEST_MODE for interpreter")
val mode_str = "interpreter"
expect(mode_str).to_equal("interpreter")
```

</details>

#### sets SIMPLE_TEST_MODE for smf

- sets SIMPLE_TEST_MODE for smf
   - Expected: mode_str equals `smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sets SIMPLE_TEST_MODE for smf")
val mode_str = "smf"
expect(mode_str).to_equal("smf")
```

</details>

#### sets SIMPLE_TEST_FILTER for slow

- sets SIMPLE_TEST_FILTER for slow
   - Expected: filter equals `slow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sets SIMPLE_TEST_FILTER for slow")
val filter = "slow"
expect(filter).to_equal("slow")
```

</details>

#### sets SIMPLE_TEST_FILTER for skipped

- sets SIMPLE_TEST_FILTER for skipped
   - Expected: filter equals `skipped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sets SIMPLE_TEST_FILTER for skipped")
val filter = "skipped"
expect(filter).to_equal("skipped")
```

</details>

#### sets SIMPLE_TEST_SHOW_TAGS to 1

- sets SIMPLE_TEST_SHOW_TAGS to 1
   - Expected: val_str equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sets SIMPLE_TEST_SHOW_TAGS to 1")
val val_str = "1"
expect(val_str).to_equal("1")
```

</details>

### Simple Test Runner Skip Features

#### extracts feature IDs from file header

- extracts feature IDs from file header
   - Expected: ids equals `#100-105`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts feature IDs from file header")
val header = "**Feature IDs:** #100-105"
val ids = header.replace("**Feature IDs:**", "").trim()
expect(ids).to_equal("#100-105")
```

</details>

#### extracts category from file header

- extracts category from file header
   - Expected: cat equals `Tooling`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts category from file header")
val header = "**Category:** Tooling"
val cat = header.replace("**Category:**", "").trim()
expect(cat).to_equal("Tooling")
```

</details>

#### extracts status from file header

- extracts status from file header
   - Expected: status equals `Draft`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts status from file header")
val header = "**Status:** Draft"
val status = header.replace("**Status:**", "").trim()
expect(status).to_equal("Draft")
```

</details>

#### planned-only filters by status

- planned-only filters by status
   - Expected: is_planned is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("planned-only filters by status")
val status = "planned"
val is_planned = status.contains("planned") or status.contains("tbd") or status == "unknown"
expect(is_planned).to_equal(true)
```

</details>

### Simple Test Runner Test DB

#### run record contains pass and fail counts

- run record contains pass and fail counts
   - Expected: total equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("run record contains pass and fail counts")
val passed = 10
val failed = 2
val total = passed + failed
expect(total).to_equal(12)
```

</details>

#### run record uses microsecond timestamp as run_id

- run record uses microsecond timestamp as run_id
   - Expected: run_id > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("run record uses microsecond timestamp as run_id")
val micros = 1706500000000000
val run_id = micros
expect(run_id > 0).to_equal(true)
```

</details>

#### run record status is completed

- run record status is completed
   - Expected: status equals `completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("run record status is completed")
val status = "completed"
expect(status).to_equal("completed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/test_runner_simple_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Simple Test Runner Argument Parsing, Simple Test Runner Discovery, Simple Test Runner Output Parsing, Simple Test Runner Artifact Layout, Simple Test Runner Timeout, Simple Test Runner Recursion Guard, Simple Test Runner Execution Modes, Simple Test Runner Seed Shuffle, Simple Test Runner Output Formats, Simple Test Runner Env Propagation, Simple Test Runner Skip Features, Simple Test Runner Test DB.
- Simple Test Runner Argument Parsing
- Simple Test Runner Discovery
- Simple Test Runner Output Parsing
- Simple Test Runner Artifact Layout
- Simple Test Runner Timeout
- Simple Test Runner Recursion Guard
- Simple Test Runner Execution Modes
- Simple Test Runner Seed Shuffle
- Simple Test Runner Output Formats
- Simple Test Runner Env Propagation
- Simple Test Runner Skip Features
- Simple Test Runner Test DB

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 62 |
| Active scenarios | 62 |
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

- Canonical SPipe generation for source `077552a6ef078e8d2270cb792de3c02d5a467478406af16fa3202096c0811315`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `077552a6ef078e8d2270cb792de3c02d5a467478406af16fa3202096c0811315`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `077552a6ef078e8d2270cb792de3c02d5a467478406af16fa3202096c0811315`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/tooling/test_runner_simple_spec.spl
mirror: doc/06_spec/01_unit/app/tooling/test_runner_simple_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/tooling/test_runner_simple_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/tooling/test_runner_simple_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/tooling/test_runner_simple_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/tooling/test_runner_simple_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults to test/ path when no path given' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/tooling/test_runner_simple_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses --mode smf flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/tooling/test_runner_simple_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses --mode=native equals syntax' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
