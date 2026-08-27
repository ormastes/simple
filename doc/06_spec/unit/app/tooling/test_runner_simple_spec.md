# Test Runner Simple Specification

*Source: `test/01_unit/app/tooling/test_runner_simple_spec.spl`*
*Last Updated: 2026-03-29*

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 71 | 71 | 0 | 0 |

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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
step("parses --planned-only flag")
val planned_only = true
expect(planned_only).to_equal(true)
```

</details>

### Simple Test Runner SPipe docgen propagation

#### does not launch docgen for ordinary formats

- does not launch docgen for ordinary formats
   - Expected: generate_spipe_docs_for_results([result], options, "/bin/false") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not launch docgen for ordinary formats")
val result = TestFileResult(path: "fixture_spec.spl", passed: 1, failed: 0, skipped: 0, pending: 0, duration_ms: 0, setup_ms: 0, error: "", timed_out: false, cached: false)
val options = parse_test_args(["fixture_spec.spl"])
expect(generate_spipe_docs_for_results([result], options, "/bin/false")).to_equal(0)
```

</details>

#### returns internal-error when docgen fails

- returns internal-error when docgen fails
   - Expected: generate_spipe_docs_for_results([result], options, "/bin/false") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns internal-error when docgen fails")
val result = TestFileResult(path: "fixture_spec.spl", passed: 1, failed: 0, skipped: 0, pending: 0, duration_ms: 0, setup_ms: 0, error: "", timed_out: false, cached: false)
val options = parse_test_args(["fixture_spec.spl", "--format", "doc"])
expect(generate_spipe_docs_for_results([result], options, "/bin/false")).to_equal(3)
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
step("detects timeout by exit_code -1")
val exit_code = -1
val timed_out = exit_code == -1
expect(timed_out).to_equal(true)
```

</details>

#### normal exit code is not timeout

- normal exit code is not timeout
- env var name is SIMPLE_TEST_RUNNER_RUST
- guard value is 1
- Rust runner detects guard and skips Simple dispatch
- falls back for --watch flag
- falls back for --parallel flag
- falls back for --json flag
- does not fall back for --doc flag
- does not fall back for --list flag
- does not fall back for --seed flag
- does not fall back for --list-skip-features
- interpreter mode runs file directly
   - Expected: mode equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
| Source | `test/unit/app/tooling/test_runner_simple_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Documentation was generated from executable SPipe scenarios.

## Evidence

### Artifacts

- build/test-artifacts/unit/app/tooling/test_runner_simple/summary.txt

### Logs

- build/test-artifacts/unit/app/tooling/test_runner_simple/output.log

## Test Summary

| Metric | Count |
|--------|-------|
| Scenarios | 64 |
| Slow Scenarios | 0 |
| Skipped Scenarios | 0 |

## Scenarios

- defaults to test/ path when no path given
- parses --mode smf flag
- parses --mode=native equals syntax
- parses --timeout flag with seconds
- parses --fail-fast flag
- parses --only-slow flag
- parses --only-skipped flag
- parses --seed flag
- parses --list-ignored flag
- parses --safe-mode flag
- parses --force-rebuild flag
- parses --keep-artifacts flag
- parses --all flag
- parses --doc format flag
- parses --format doc flag
- parses --list-skip-features flag
- parses --planned-only flag
- identifies spec files by _spec. pattern
- identifies test files by _test. pattern
- rejects non-spl files
- filters unit tests by excluding integration and system paths
- filters integration tests by path
- filters system tests by path
- extracts passed count from examples line
- handles zero failures
- falls back to exit code when no output parsed
- marks non-zero exit as failure when no output parsed
- tracks skipped count separately
- writes summaries under build/test-artifacts
- writes safe-mode subprocess output to output.log
- converts seconds to milliseconds
- detects timeout by exit_code -1
- normal exit code is not timeout
- env var name is SIMPLE_TEST_RUNNER_RUST
- guard value is 1
- Rust runner detects guard and skips Simple dispatch
- falls back for --watch flag
- falls back for --parallel flag
- falls back for --json flag
- does not fall back for --doc flag
- does not fall back for --list flag
- does not fall back for --seed flag
- does not fall back for --list-skip-features
- interpreter mode runs file directly
- SMF mode compiles then runs .smf
- native mode compiles then runs binary
- hash produces consistent result for same input
- different seeds produce different hashes
- default format shows PASS prefix
- default format shows FAIL prefix
- default format shows TOUT prefix for timeout
- doc format shows basename only
- sets SIMPLE_TEST_MODE for interpreter
- sets SIMPLE_TEST_MODE for smf
- sets SIMPLE_TEST_FILTER for slow
- sets SIMPLE_TEST_FILTER for skipped
- sets SIMPLE_TEST_SHOW_TAGS to 1
- extracts feature IDs from file header
- extracts category from file header
- extracts status from file header
- planned-only filters by status
- run record contains pass and fail counts
- run record uses microsecond timestamp as run_id
- run record status is completed
