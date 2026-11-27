# Single runner directory target

Executable `test/02_integration/app/test_runner/single_runner_directory_target_spec.spl`, SHA-256 `b125b1c8f760991806ae3123b6143720ee4b7ea32c94f375c06760701c5ff5cb`.

## Workflow

1. Build a temporary fixture directory holding one passing and one failing trivial BDD spec; run `bin/simple test <dir> --no-session-daemon --sequential`. The run must exit 1, print both files' own `PASS`/`FAIL` lines, and aggregate `Files: 2 / Passed: 1 / Failed: 1` under a `Directory Test Summary`.
2. Build a directory of two passing specs; the same invocation must exit 0 with `Passed: 2`.
3. Run the same invocation against an empty directory; it must exit 1 with an explicit `no *_spec.spl files found` error — never a silent green.

REQ-TEST-DIR-001: the `--no-session-daemon` lane must accept a directory target, run each discovered `*_spec.spl` through the unchanged per-file machinery in one process (paying the runner's fixed module-load cost once per process, not once per file), and fail closed when nothing is discovered. This closes the directory half of doc/08_tracking/bug/test_invocation_fixed_setup_cost_caps_every_sweep_2026-08-17.md; the daemon lane's per-request worker resolution remains governed by that bug's seed-side unblock condition.

## Hosted evidence (2026-11-12, Rust seed, worktree lane)

- New spec: `test ... --no-session-daemon --sequential --timeout 300` → `3 examples, 0 failures`, `SPEC FILE VERDICT ... executed=3 passed=3 failed=0 dropped=0`, PASS.
- Probe: `test test/01_unit/_mcdc_probe --no-session-daemon` (3 specs, one failing) → full run 2.1s wall vs 85s for the same directory through the full runner; correct per-file PASS/FAIL and aggregate exit 1.

<details><summary>Executable SSpec</summary>

```simple
"""
## Purpose and audience
Test-runner maintainers ensure the single-file lane (`--no-session-daemon`)
accepts a directory target and runs every discovered spec through the
per-file machinery in one process, instead of rejecting the directory and
forcing sweeps onto a path that re-pays the runner's fixed module-load cost
per file (doc/08_tracking/bug/test_invocation_fixed_setup_cost_caps_every_sweep_2026-08-17.md).
## Operator workflow
Run with the production binary as bin/simple (or SIMPLE_TEST_BINARY override).
Each example builds a temporary fixture directory, invokes
`bin/simple test <dir> --no-session-daemon --sequential`, and asserts on the
real exit code and summary output.
## Compatibility and limitations
Nested runs pay the runner's own startup once per example; fixture specs are
trivial BDD files written to a unique /tmp directory and removed afterwards.
## Verification guidance and troubleshooting
A mixed pass/fail directory must exit nonzero and still report both files;
an all-pass directory must exit zero; an empty directory must fail closed.
"""
# Lifecycle: doc/08_tracking/bug/test_invocation_fixed_setup_cost_caps_every_sweep_2026-08-17.md
# @manual_section: single runner directory target
# @evidence-display: links
use std.spec.*
use app.io.process_ops.{process_run_bounded}
use std.io_runtime.{env_get}
use std.io_runtime.{getpid}
use std.io_runtime.{time_now_unix_micros}
use std.io_runtime.{dir_create_all}
use std.io_runtime.{dir_remove_all}
use std.io_runtime.{file_write}

fn contract_binary() -> text:
    val configured = env_get("SIMPLE_TEST_BINARY") ?? ""
    if configured != "":
        return configured
    "bin/simple"

fn fresh_fixture_dir(label: text) -> text:
    val dir = "/tmp/single_runner_dir_target_{label}_{getpid()}_{time_now_unix_micros()}"
    dir_create_all(dir)
    dir

fn write_spec(dir: text, name: text, body: text):
    file_write("{dir}/{name}", body)

fn run_dir(binary: text, dir: text) -> (text, i64):
    val (out, err, code) = process_run_bounded(binary,
        ["test", dir, "--no-session-daemon", "--sequential", "--timeout", "120"],
        300000, 1048576)
    (out + err, code)

val PASSING_SPEC = "describe \"fixture alpha\":\n    it \"passes\":\n        expect(true).to_equal(true)\n"
val FAILING_SPEC = "describe \"fixture beta\":\n    it \"fails\":\n        expect(true).to_equal(false)\n"

describe "the single-file lane accepts directory targets":
    it "runs every discovered spec and aggregates per-file verdicts":
        # @req REQ-TEST-DIR-001
        # @capture(exec): real mixed-pass/fail directory run exit code and summary
        step("Build a fixture directory with one passing and one failing spec")
        val dir = fresh_fixture_dir("mixed")
        write_spec(dir, "alpha_spec.spl", PASSING_SPEC)
        write_spec(dir, "beta_spec.spl", FAILING_SPEC)
        step("Run the directory target through the single-file lane")
        val result = run_dir(contract_binary(), dir)
        step("Require a nonzero exit while BOTH files report their own verdict")
        expect(result.1).to_equal(1)
        expect(result.0).to_contain("PASS {dir}/alpha_spec.spl")
        expect(result.0).to_contain("FAIL {dir}/beta_spec.spl")
        step("Require the directory summary to count both files honestly")
        expect(result.0).to_contain("Directory Test Summary")
        expect(result.0).to_contain("Files: 2")
        expect(result.0).to_contain("Passed: 1")
        expect(result.0).to_contain("Failed: 1")
        dir_remove_all(dir)

    it "returns zero when every discovered spec passes":
        # @req REQ-TEST-DIR-001
        # @capture(exec): real all-pass directory run exit code and summary
        step("Build a fixture directory with two passing specs")
        val dir = fresh_fixture_dir("allpass")
        write_spec(dir, "one_spec.spl", PASSING_SPEC)
        write_spec(dir, "two_spec.spl", PASSING_SPEC)
        step("Run the directory target through the single-file lane")
        val result = run_dir(contract_binary(), dir)
        step("Require a clean exit and an honest aggregate")
        expect(result.1).to_equal(0)
        expect(result.0).to_contain("Files: 2")
        expect(result.0).to_contain("Passed: 2")
        expect(result.0).to_contain("Failed: 0")
        dir_remove_all(dir)

    it "fails closed on a directory containing no specs":
        # @req REQ-TEST-DIR-001
        # @capture(exec): real empty-directory run exit code and error line
        step("Build an empty fixture directory")
        val dir = fresh_fixture_dir("empty")
        step("Run the directory target through the single-file lane")
        val result = run_dir(contract_binary(), dir)
        step("Require a nonzero exit and an explicit error, never a silent green")
        expect(result.1).to_equal(1)
        expect(result.0).to_contain("no *_spec.spl files found under directory: {dir}")
        dir_remove_all(dir)
```
</details>
