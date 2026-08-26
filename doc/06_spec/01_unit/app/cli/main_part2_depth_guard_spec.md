# Main Part2 Depth Guard Specification

> Tests covering _CliMain main_and_help depth guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Main Part2 Depth Guard Specification

## Scenarios

### _CliMain main_and_help depth guard

#### defaults malformed test depth parsing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults malformed test depth parsing
   - Expected: source does not contain `env_set("SIMPLE_TEST_DEPTH", (_depth + 1).to_text())`
   - Expected: source does not contain `_depth_str.to_int()\n`
   - Expected: source does not contain `env_set("SIMPLE_TEST_DEPTH", "\{_depth + 1\}")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("defaults malformed test depth parsing")
val source = rt_file_read_text("src/app/cli/_CliMain/main_and_help.spl") ?? ""

expect(source).to_contain("_depth_str.to_int() ?? 0")
expect(source).to_contain("env_set(\"SIMPLE_TEST_DEPTH\", \"1\")")
expect(source.contains("env_set(\"SIMPLE_TEST_DEPTH\", (_depth + 1).to_text())")).to_equal(false)
expect(source.contains("_depth_str.to_int()\n")).to_equal(false)
expect(source.contains("env_set(\"SIMPLE_TEST_DEPTH\", \"\{_depth + 1\}\")")).to_equal(false)
```

</details>

#### routes tests through the pure-Simple runner

- routes tests through the pure-Simple runner
   - Expected: source does not contain `main as pure_test_runner_main`
   - Expected: source does not contain `cli_run_tests_process_args`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("routes tests through the pure-Simple runner")
val source = rt_file_read_text("src/app/cli/_CliMain/main_and_help.spl") ?? ""

# `use` or `use lazy` both satisfy the routing contract; the module path
# and the imported symbol are what matter.
expect(source).to_contain("app.test_runner_new.test_runner_main.\{run_test_cli\}")
expect(source).to_contain("return run_test_cli()")
expect(source.contains("main as pure_test_runner_main")).to_equal(false)
expect(source.contains("cli_run_tests_process_args")).to_equal(false)
```

</details>

#### reads executable identity in-process, never via the unregistered scalar argv externs

- reads executable identity in-process, never via the unregistered scalar argv externs
   - Expected: source does not contain `rt_cli_current_exe_path`
   - Expected: source does not contain `extern fn rt_cli_arg_count`
   - Expected: source does not contain `extern fn rt_cli_arg_at`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reads executable identity in-process, never via the unregistered scalar argv externs")
val source = rt_file_read_text("src/app/io/cli_ops.spl") ?? ""

# Contract per cli_symlink_argv0_seed_sibling_lookup_2026-07-24.md:
# prefer the kernel's record of the real executable, canonicalized
# IN-PROCESS via rt_path_absolute (never a `readlink -f` shell-out,
# which describes the helper and caused unbounded self-delegation),
# then fall back to sys_get_args(). rt_cli_arg_count/rt_cli_arg_at are
# unregistered on the deployed seed (#159) and must not be declared.
expect(source).to_contain("val self_path = _cli_resolve_symlink(\"/proc/self/exe\")")
expect(source).to_contain("rt_path_absolute(path) ?? \"\"")
expect(source).to_contain("val all_args = sys_get_args()")
expect(source.contains("rt_cli_current_exe_path")).to_equal(false)
expect(source.contains("extern fn rt_cli_arg_count")).to_equal(false)
expect(source.contains("extern fn rt_cli_arg_at")).to_equal(false)
```

</details>

#### stages code through the compatible file writer

- stages code through the compatible file writer
   - Expected: source does not contain `extern fn rt_file_write_text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("stages code through the compatible file writer")
val source = rt_file_read_text("src/app/io/_CliCommands/run_commands.spl") ?? ""

expect(source).to_contain("use app.io.file_ops.\{file_write\}")
expect(source).to_contain("val main_source = \"fn main():\\n    \"")
expect(source).to_contain("if not file_write(tmp_path, main_source):")
expect(source.contains("extern fn rt_file_write_text")).to_equal(false)
```

</details>

#### copies delegated program arguments into an owned argv vector

- copies delegated program arguments into an owned argv vector
   - Expected: source does not contain `startup_normalize_program_args(path, args)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("copies delegated program arguments into an owned argv vector")
val source = rt_file_read_text("src/app/io/_CliCommands/run_commands.spl") ?? ""

expect(source).to_contain("var driver_args: [text] = [path]")
expect(source).to_contain("for arg in args:\n            driver_args.push(arg)")
expect(source.contains("startup_normalize_program_args(path, args)")).to_equal(false)
```

</details>

#### returns from the SMF loader branch without source fallback

- returns from the SMF loader branch without source fallback
   - Expected: source does not contain `if path.ends_with(".smf"):\n        match moduleloader_execute_smf(path):`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns from the SMF loader branch without source fallback")
val source = rt_file_read_text("src/app/io/_CliCommands/run_commands.spl") ?? ""

expect(source).to_contain("if path.ends_with(\".smf\"):\n        return match moduleloader_execute_smf(path):")
expect(source.contains("if path.ends_with(\".smf\"):\n        match moduleloader_execute_smf(path):")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/main_part2_depth_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering _CliMain main_and_help depth guard.
- _CliMain main_and_help depth guard

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b2694da085df6cccbdb05e9caab696b049e05cbd2021c7f9e6c6057edef714a2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b2694da085df6cccbdb05e9caab696b049e05cbd2021c7f9e6c6057edef714a2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b2694da085df6cccbdb05e9caab696b049e05cbd2021c7f9e6c6057edef714a2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/cli/main_part2_depth_guard_spec.spl
mirror: doc/06_spec/01_unit/app/cli/main_part2_depth_guard_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/app/cli/main_part2_depth_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/main_part2_depth_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/main_part2_depth_guard_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/cli/main_part2_depth_guard_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults malformed test depth parsing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/main_part2_depth_guard_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes tests through the pure-Simple runner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/main_part2_depth_guard_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads executable identity in-process, never via the unregistered scalar argv externs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
