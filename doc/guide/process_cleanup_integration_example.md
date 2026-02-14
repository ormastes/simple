# Process Cleanup Integration Example

This document shows how to integrate the robust process/container cleanup system into the existing test runner.

## Integration Points

### 1. Add Lifecycle Imports

**File:** `src/app/test_runner_new/test_runner_main.spl`

```simple
# Add to existing imports (around line 31)
use app.test_runner_new.runner_lifecycle.{
    lifecycle_enable_heartbeat,
    lifecycle_send_heartbeat,
    cleanup_all_children
}
```

### 2. Enable Heartbeat on Startup

**Location:** Start of `run_tests()` function (around line 61)

```simple
fn run_tests(options: TestOptions) -> TestRunResult:
    # Enable heartbeat monitoring if self-protection enabled
    if options.self_protect:
        lifecycle_enable_heartbeat()
        print "Heartbeat monitoring enabled"
        print ""

    # ... rest of existing code ...
```

### 3. Send Heartbeat in Main Loop

**Location:** Inside main test loop (around line 125-150)

```simple
for file_path in files:
    # ... existing resource check code ...

    # Run test
    val result = run_single_test(file_path, options)
    print_result(result, options.format)

    # ... existing result accumulation code ...

    # Send heartbeat after each test
    if options.self_protect:
        lifecycle_send_heartbeat()

    # ... fail_fast check ...
```

### 4. Cleanup on Normal Exit

**Location:** End of `run_tests()` function (around line 161)

```simple
    # Clean up checkpoint on successful completion
    if options.resume and checkpoint_exists():
        checkpoint_delete()

    # Cleanup any tracked processes/containers on normal exit
    val cleaned = cleanup_all_children()
    if cleaned > 0:
        print "Cleaned up {cleaned} orphaned resources"

    TestRunResult(
        files: results,
        total_passed: total_passed,
        # ... etc ...
    )
```

### 5. Use Tracked Spawns in Execute Functions

**File:** `src/app/test_runner_new/test_runner_execute.spl`

Replace direct `process_run_timeout()` calls with tracked spawns for async execution.

**Current code (line 289):**
```simple
fn run_test_file_interpreter(file_path: text, options: TestOptions) -> TestFileResult:
    # ...
    var (stdout, stderr, exit_code) = process_run_timeout(binary, child_args, timeout_ms)
    # ...
```

**Enhanced version (future - requires refactor):**
```simple
use app.test_runner_new.runner_lifecycle.{spawn_tracked_process, untrack_process}

fn run_test_file_interpreter(file_path: text, options: TestOptions) -> TestFileResult:
    val binary = find_simple_binary()
    val child_args = build_child_args(file_path, options)
    val timeout_ms = options.timeout * 1000
    val start = time_now_unix_micros()

    # Spawn with tracking
    val pid = spawn_tracked_process(binary, child_args)

    # Wait for completion with timeout
    val exit_code = process_wait(pid, timeout_ms)

    # Untrack after successful wait
    untrack_process(pid)

    val end = time_now_unix_micros()
    val duration_ms = (end - start) / 1000

    # NOTE: Need to capture stdout/stderr - requires SFFI additions
    # For now, this is a future enhancement
```

### 6. Container Test Cleanup

**File:** `src/app/test_runner_new/sequential_container.spl`

```simple
use app.test_runner_new.runner_lifecycle.{
    run_tracked_container,
    stop_tracked_container
}

fn sequential_container_run_single_test(
    test_file: text,
    config: SequentialContainerConfig
) -> TestFileResult:
    # ... existing code ...

    # Use tracked container run
    val container_id = run_tracked_container(
        config.runtime,
        config.base_image,
        ["test", test_file],
        config.memory_mb,
        config.cpu_limit
    )

    # ... wait for completion ...

    # Cleanup container
    stop_tracked_container(container_id)

    # ... return result ...
```

## Complete Example: Enhanced Main Loop

Here's a complete example of the enhanced main test loop:

```simple
fn run_tests(options: TestOptions) -> TestRunResult:
    # Enable lifecycle management
    if options.self_protect:
        lifecycle_enable_heartbeat()

    # Load checkpoint if resuming
    var ckpt_passed = 0
    var ckpt_failed = 0
    var ckpt_skipped = 0

    val all_files = discover_test_files(options.path, options)
    var files = all_files

    if options.resume and checkpoint_exists():
        val ckpt = checkpoint_load()
        ckpt_passed = ckpt.total_passed
        ckpt_failed = ckpt.total_failed
        ckpt_skipped = ckpt.total_skipped
        files = checkpoint_skip_completed(all_files, ckpt)
        print "Resuming from checkpoint..."
        print ""

    if files.len() == 0:
        print "No test files found"
        return make_empty_result()

    propagate_env_vars(options)

    print "Running {files.len()} test file(s)..."
    print ""

    var results: [TestFileResult] = []
    var total_passed = ckpt_passed
    var total_failed = ckpt_failed
    var total_skipped = ckpt_skipped
    var total_pending = 0
    var total_timed_out = 0
    var total_duration_ms = 0
    var completed_files: [text] = []
    var tests_run = 0

    for file_path in files:
        # Resource check every 5 tests
        if options.self_protect and tests_run % 5 == 0 and tests_run > 0:
            val (violated, reason) = system_exceeds_threshold(
                options.cpu_threshold,
                options.mem_threshold
            )
            if violated:
                # Graceful shutdown - never returns
                # Saves checkpoint and cleans up all children
                shutdown_graceful(
                    reason,
                    completed_files,
                    total_passed,
                    total_failed,
                    total_skipped
                )

        # Periodic checkpoint every 10 tests
        if options.self_protect and tests_run % 10 == 0 and tests_run > 0:
            checkpoint_save(
                completed_files,
                total_passed,
                total_failed,
                total_skipped,
                "periodic"
            )

        # Run test
        val result = run_single_test(file_path, options)
        print_result(result, options.format)

        # Accumulate results
        total_passed = total_passed + result.passed
        total_failed = total_failed + result.failed
        total_skipped = total_skipped + result.skipped
        total_pending = total_pending + result.pending
        if result.timed_out:
            total_timed_out = total_timed_out + 1
        total_duration_ms = total_duration_ms + result.duration_ms

        results.push(result)
        completed_files.push(file_path)
        tests_run = tests_run + 1

        # Send heartbeat
        if options.self_protect:
            lifecycle_send_heartbeat()

        # Fail fast check
        if options.fail_fast and (result.failed > 0 or result.timed_out):
            print ""
            print "Stopping early (--fail-fast)"
            break

    # Normal exit cleanup
    if options.resume and checkpoint_exists():
        checkpoint_delete()

    # Cleanup any orphaned resources
    val cleaned = cleanup_all_children()
    if cleaned > 0:
        print ""
        print "[CLEANUP] Cleaned up {cleaned} orphaned resources"

    TestRunResult(
        files: results,
        total_passed: total_passed,
        total_failed: total_failed,
        total_skipped: total_skipped,
        total_pending: total_pending,
        total_timed_out: total_timed_out,
        total_duration_ms: total_duration_ms
    )
```

## Testing the Integration

### 1. Normal Exit (No Cleanup Needed)

```bash
$ bin/simple test test/unit/std/
Running 150 test file(s)...
...
Tests complete: 1500 passed, 0 failed
```

### 2. Graceful Shutdown (Resource Limit)

```bash
$ bin/simple test --self-protect --cpu-limit=80 test/
Running 500 test file(s)...
Self-protection enabled (CPU: 80%, Memory: 90%)
...
[150/500 tests complete]

=========================================
GRACEFUL SHUTDOWN INITIATED
=========================================
Reason: cpu
Completed tests: 150
Passed: 1450, Failed: 10, Skipped: 5

[SHUTDOWN] Step 1/4: Saving checkpoint...
[SHUTDOWN] Checkpoint saved successfully

[SHUTDOWN] Step 2/4: Killing child processes...
[SHUTDOWN] Killed 3 processes

[SHUTDOWN] Step 3/4: Stopping containers...
[SHUTDOWN] Stopped 0 containers

[SHUTDOWN] Step 4/4: Exiting with code 42

=========================================
GRACEFUL SHUTDOWN COMPLETE
=========================================

To resume tests, run:
  simple test --resume
```

### 3. Resume from Checkpoint

```bash
$ bin/simple test --resume
Resuming from checkpoint (reason: cpu)
Previous progress: 1450 passed, 10 failed, 5 skipped

Running 350 test file(s)...
...
Tests complete: 3450 passed, 15 failed
```

### 4. Ctrl+C Cleanup (Future - Requires Signal Handling)

```bash
$ bin/simple test test/
Running 500 test file(s)...
...
^C
[SIGNAL] SIGINT received

[LIFECYCLE] Cleaning up all child processes and containers...
[LIFECYCLE] Killed 5 processes, stopped 2 containers
[LIFECYCLE] Cleanup complete (7 resources)

Interrupted by user
```

## Migration Checklist

- [x] Create `process_tracker.spl`
- [x] Create `checkpoint.spl`
- [x] Create `runner_lifecycle.spl`
- [ ] Add imports to `test_runner_main.spl`
- [ ] Enable heartbeat in `run_tests()`
- [ ] Add heartbeat sends in main loop
- [ ] Add cleanup on normal exit
- [ ] Update `test_runner_execute.spl` for tracked spawns (requires refactor)
- [ ] Update `sequential_container.spl` for tracked containers
- [ ] Add signal handlers (requires SFFI additions)
- [ ] Test end-to-end scenarios
- [ ] Update documentation

## Notes

### Current Limitations

1. **Synchronous Execution:** Current `process_run_timeout()` doesn't expose PIDs, so we can't track synchronous executions. This is OK for now - cleanup happens on shutdown anyway.

2. **No Signal Handlers:** Phase 2 (signal handling) requires SFFI additions. Until then, Ctrl+C cleanup won't work.

3. **No Stdout/Stderr Capture:** Tracked async spawns would need separate stdout/stderr capture mechanism.

### Future Enhancements

Once SFFI signal handling is available:

```simple
# In main.spl entry point
fn main():
    install_signal_handlers()  # Install SIGTERM/SIGINT/SIGHUP handlers
    run_test_runner()
    # Cleanup happens automatically via signal handlers

fn install_signal_handlers():
    rt_signal_handler_install(15, on_sigterm)
    rt_signal_handler_install(2, on_sigint)
    rt_signal_handler_install(1, on_sighup)
    rt_atexit_register(on_normal_exit)

fn on_sigterm():
    cleanup_and_exit(143, "SIGTERM")

fn on_sigint():
    cleanup_and_exit(130, "SIGINT (Ctrl+C)")

fn on_normal_exit():
    cleanup_all_children()
```

## References

- `src/app/test_runner_new/process_tracker.spl`
- `src/app/test_runner_new/runner_lifecycle.spl`
- `src/app/test_runner_new/checkpoint.spl`
- `src/app/test_runner_new/shutdown.spl`
- `doc/guide/robust_process_cleanup.md`
