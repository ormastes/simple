# Robust Test Runner - Complete Implementation Plan

**Date:** 2026-02-14
**Status:** Implementation Plan
**Author:** Claude Sonnet 4.5

---

## Executive Summary

This plan consolidates and extends the robust test runner implementation across 5 phases, building on completed container testing infrastructure (Phase 2) and resource monitoring (Phase 3). The goal is a production-grade test infrastructure with process isolation, container isolation, resource enforcement, and distributed execution.

**Current State:**
- Container testing infrastructure: COMPLETE (8 deliverables, 82KB docs/scripts)
- Resource monitoring: COMPLETE (3 modules, 27 tests, 100% passing)
- Process limits: STUB (process_run_with_limits warns but doesn't enforce)
- Test runner: 4,067/4,067 tests passing, 17.4s execution time

**Target State:**
- Enforced process resource limits (CPU, memory, FDs)
- Container-based isolation for critical tests
- Real-time resource monitoring with violation detection
- Hybrid execution (native/process/container)
- Sequential container mode for maximum isolation
- Production-grade diagnostics and reporting

---

## Phase 1: Process Resource Enforcement

**Duration:** 3-4 days
**Effort:** ~10-12 hours implementation + 4-5 hours testing
**Dependencies:** None
**Risk:** Low
**Status:** NOT STARTED

### 1.1 Implement Real process_run_with_limits()

**Objective:** Replace stub implementation with actual ulimit-based resource enforcement.

**File:** `src/app/io/mod.spl`

**Current Implementation (stub):**
```simple
fn process_run_with_limits(cmd: text, cpu_ms: i64, mem_mb: i64) -> ProcessResult:
    print "WARNING: Resource limits not enforced - falling back to process_run()"
    process_run(cmd)
```

**New Implementation:**

```simple
fn process_run_with_limits(cmd: text, cpu_ms: i64, mem_mb: i64) -> ProcessResult:
    # Platform check
    if is_windows():
        print "WARNING: Resource limits not supported on Windows"
        return process_run(cmd)

    # Convert limits
    val timeout_sec = cpu_ms / 1000
    val mem_kb = mem_mb * 1024

    # Build ulimit wrapper (POSIX sh syntax)
    val wrapped_cmd = "sh -c 'ulimit -v {mem_kb}; ulimit -t {timeout_sec}; exec {cmd}'"

    # Add timeout wrapper with buffer (wall-clock enforcement)
    val timeout_buffer = timeout_sec + 5
    val final_cmd = "timeout --kill-after=5s {timeout_buffer}s {wrapped_cmd}"

    # Execute
    val result = process_run(final_cmd)

    # Detect violations (enhanced ProcessResult needed)
    var limit_exceeded = false
    var limit_type = ""

    if result.exit_code == 124:  # timeout(1) SIGTERM
        limit_exceeded = true
        limit_type = "timeout"
    else if result.exit_code == 137:  # SIGKILL
        limit_exceeded = true
        limit_type = "timeout_hard"
    else if result.exit_code == 139:  # SIGSEGV (often memory)
        limit_exceeded = true
        limit_type = "memory"
    else if result.stderr.contains("CPU time limit exceeded"):
        limit_exceeded = true
        limit_type = "cpu"
    else if result.stderr.contains("Cannot allocate memory"):
        limit_exceeded = true
        limit_type = "memory"

    # Return enhanced result
    # NOTE: ProcessResult struct needs limit_exceeded and limit_type fields
    return result  # TODO: wrap in enhanced struct
```

**Changes Required:**

1. **Update ProcessResult struct** (if not already done):
   ```simple
   class ProcessResult:
       exit_code: i64
       stdout: text
       stderr: text
       success: bool
       limit_exceeded: bool    # NEW
       limit_type: text        # NEW: "timeout", "cpu", "memory", ""
   ```

2. **Add platform detection helpers** (if not already in std.platform):
   ```simple
   fn is_windows() -> bool:
       val os = env_get("OS") ?? ""
       return os.contains("Windows")

   fn is_unix() -> bool:
       return not is_windows()
   ```

3. **Add ulimit validation**:
   ```simple
   fn validate_ulimits() -> bool:
       # Test if ulimit works
       val test = process_run("sh -c 'ulimit -v 1024; exit 0'")
       return test.exit_code == 0
   ```

**Testing:**

Create `test/unit/app/io/process_limits_enforcement_spec.spl`:

```simple
use std.spec.{describe, it, expect, slow_it}
use app.io.mod.{process_run_with_limits}

describe "process_run_with_limits enforcement":
    slow_it "enforces CPU time limit":
        # Infinite CPU loop
        val result = process_run_with_limits(
            "bash -c 'while true; do :; done'",
            cpu_ms: 2000,  # 2 seconds
            mem_mb: 100
        )
        expect(result.limit_exceeded).to_equal(true)
        val type_ok = result.limit_type == "cpu" or result.limit_type == "timeout"
        expect(type_ok).to_equal(true)

    slow_it "enforces memory limit":
        # Allocate ~200MB (exceeds 50MB limit)
        val result = process_run_with_limits(
            "python3 -c 'x = [0] * (50 * 1024 * 1024)'",
            cpu_ms: 10000,
            mem_mb: 50
        )
        expect(result.limit_exceeded).to_equal(true)
        expect(result.limit_type).to_equal("memory")

    it "succeeds within limits":
        val result = process_run_with_limits(
            "echo 'hello world'",
            cpu_ms: 5000,
            mem_mb: 100
        )
        expect(result.success).to_equal(true)
        expect(result.limit_exceeded).to_equal(false)
        expect(result.stdout).to_contain("hello world")

    slow_it "enforces timeout (wall-clock)":
        # Sleep exceeds CPU time (won't trigger ulimit -t)
        val result = process_run_with_limits(
            "sleep 10",
            cpu_ms: 1000,  # 1 second limit
            mem_mb: 100
        )
        expect(result.limit_exceeded).to_equal(true)
        expect(result.limit_type).to_contain("timeout")
```

**Success Criteria:**
- [ ] ProcessResult struct extended with limit_exceeded, limit_type
- [ ] process_run_with_limits() enforces CPU limits (±10% accuracy)
- [ ] process_run_with_limits() enforces memory limits (±10% accuracy)
- [ ] Wall-clock timeout works for sleep/blocking ops
- [ ] Limit violations detected and reported correctly
- [ ] 15+ test cases passing (CPU, memory, timeout, success)
- [ ] Windows fallback works (graceful degradation)

**Files to Modify:**
- `src/app/io/mod.spl` - Implement enforcement (~50 lines)
- `test/unit/app/io/process_limits_enforcement_spec.spl` - Tests (NEW, ~100 lines)

**Blockers:** None

**Complexity:** Medium (ulimit behavior varies across shells)

---

### 1.2 Integration with Test Runner

**Objective:** Use enforced limits in test runner execution modes.

**File:** `src/app/test_runner_new/test_runner_execute.spl`

**Changes:**

1. **Update run_test_file_safe_mode()** (~line 180):
   ```simple
   fn run_test_file_safe_mode(file_path: text, options: TestOptions) -> TestFileResult:
       # Get resource profile (from config or slow_it marker)
       val profile = get_resource_profile(file_path, options)

       # Build test command
       val binary = get_simple_binary()
       val args = build_test_args(file_path, options)
       val test_cmd = "{binary} {args}"

       # Run with enforced limits
       val result = process_run_with_limits(
           test_cmd,
           cpu_ms: profile.cpu_ms,
           mem_mb: profile.mem_mb
       )

       # Check for violations
       if result.limit_exceeded:
           return TestFileResult(
               file_path: file_path,
               status: "failed",
               error: "Resource limit exceeded: {result.limit_type}",
               duration_ms: profile.timeout_ms,
               tests_run: 0,
               tests_passed: 0,
               tests_failed: 1
           )

       # Parse normal output
       return parse_test_output(result.stdout, file_path)
   ```

2. **Add get_resource_profile() helper**:
   ```simple
   fn get_resource_profile(file_path: text, options: TestOptions) -> ResourceProfile:
       # Check CLI override
       if options.profile != "":
           return profile_from_name(options.profile)

       # Check for slow_it marker in file
       val content = file_read(file_path)
       if content.contains("slow_it"):
           return profile_slow()

       # Check file path patterns
       if file_path.contains("/integration/"):
           return profile_standard()
       if file_path.contains("/unit/"):
           return profile_fast()

       # Default
       return profile_standard()
   ```

3. **Import resource profiles**:
   ```simple
   use std.process_limits.{ResourceProfile, profile_fast, profile_standard, profile_slow}
   use std.process_limits.{profile_from_name}
   ```

**Testing:**

Add to `test/unit/app/test_runner_new/test_runner_execute_spec.spl`:

```simple
describe "test_runner_execute with resource limits":
    slow_it "detects CPU limit violations":
        # Create test file that loops infinitely
        temp_write("cpu_loop_spec.spl", r"
use std.spec.{describe, it}
describe 'CPU loop':
    it 'loops forever':
        while true:
            pass_do_nothing
")
        val options = TestOptions(mode: "safe", profile: "fast")
        val result = run_test_file_safe_mode(temp_file("cpu_loop_spec.spl"), options)

        expect(result.status).to_equal("failed")
        expect(result.error).to_contain("Resource limit exceeded")
        expect(result.error).to_contain("cpu")

    it "applies slow profile to slow_it tests":
        temp_write("slow_test_spec.spl", r"
use std.spec.{describe, slow_it}
describe 'Slow test':
    slow_it 'takes time':
        var sum = 0
        for i in 10000000:
            sum = sum + i
")
        val options = TestOptions(mode: "safe")
        val result = run_test_file_safe_mode(temp_file("slow_test_spec.spl"), options)

        # Should use slow profile (30s), not fast (1s)
        expect(result.status).to_equal("passed")
```

**Success Criteria:**
- [ ] Safe mode uses enforced limits
- [ ] Resource profiles applied based on markers
- [ ] CLI --profile=NAME override works
- [ ] Violations reported in TestFileResult
- [ ] 10+ integration tests passing
- [ ] No regressions in existing 4,067 tests

**Files to Modify:**
- `src/app/test_runner_new/test_runner_execute.spl` - Add limits (~80 lines)
- `test/unit/app/test_runner_new/test_runner_execute_spec.spl` - Tests (~60 lines)

**Dependencies:** 1.1 complete

**Complexity:** Low

---

## Phase 2: Container Integration (ALREADY COMPLETE)

**Status:** COMPLETE (2026-02-14)

### Summary of Completed Work

**Deliverables (8 files, 82KB):**
1. `doc/guide/container_testing.md` - Full guide (11KB)
2. `doc/guide/resource_limits.md` - Resource profiles (14KB)
3. `doc/guide/README_CONTAINER_TESTING.md` - Index (11KB)
4. `.github/workflows/containerized-tests.yml` - CI workflow (14KB)
5. `.github/workflows/test-isolation.yml` - Critical tests (13KB)
6. `scripts/ci-test.sh` - CI helper (7KB)
7. `scripts/local-container-test.sh` - Dev helper (8KB)
8. `docker-compose.yml` - Local dev config (4KB)

**Features:**
- Docker/Podman container execution
- 5 resource profiles (fast → critical)
- GitHub Actions CI/CD workflows (16 jobs)
- Helper scripts for local/CI testing
- Docker Compose for easy local dev
- Security hardening (non-root, read-only, capabilities)
- Container size: ~40MB (Alpine + Simple runtime)

**Testing:**
- Container backend: `test/unit/app/test_runner_new/container_backend_spec.spl`
- All tests pass in container environment

**See:** `doc/report/container_testing_integration_2026-02-14.md`

---

## Phase 3: Resource Monitoring & Enforcement (ALREADY COMPLETE)

**Status:** COMPLETE (2026-02-14)

### Summary of Completed Work

**Modules (3 files, ~1,080 lines):**
1. `src/std/process_monitor.spl` - Process metrics via /proc (~400 lines)
2. `src/std/resource_tracker.spl` - Database tracking (~480 lines)
3. `src/app/test_runner_new/test_runner_resources.spl` - Integration (~200 lines)

**Test Coverage (27 tests, 100% passing):**
1. `test/unit/std/process_monitor_spec.spl` - 6 tests
2. `test/unit/std/resource_tracker_spec.spl` - 11 tests
3. `test/unit/app/test_runner_new/test_runner_resources_spec.spl` - 10 tests

**Features:**
- ProcessMetrics struct (CPU, memory, FDs, threads)
- Linux /proc filesystem reading (full support)
- macOS ps command support (limited)
- Windows stub (graceful degradation)
- ResourceUsageRecord database (SDN format)
- Violation detection and reporting
- Historical tracking and queries
- Integration hooks for test runner

**Database:** `doc/test/resource_usage.sdn` (append-only)

**See:** `doc/report/phase3_resource_monitoring_implementation_2026-02-14.md`

---

## Phase 4: Hybrid Execution & Sequential Containers

**Duration:** 4-5 days
**Effort:** ~14-16 hours implementation + 6-8 hours testing
**Dependencies:** Phase 1, Phase 2, Phase 3 complete
**Risk:** Medium
**Status:** NOT STARTED

### 4.1 Execution Strategy System

**Objective:** Implement hybrid execution (native/process/container) with auto-selection.

**File:** `src/app/test_runner_new/execution_strategy.spl` (NEW, ~300 lines)

**Design:**

```simple
# Execution modes
enum ExecutionMode:
    Native           # Direct process execution (no isolation)
    Process          # Process with ulimit enforcement
    SafeMode         # Process with timeout + ulimit (current safe mode)
    Container        # Docker/Podman container isolation
    ContainerSeq     # Sequential container (max isolation)

class ExecutionStrategy:
    mode: text               # "native", "process", "safe", "container", "container_seq"
    profile: ResourceProfile
    container_image: text
    container_runtime: text  # "docker" or "podman"

fn strategy_auto_select(
    test_file: text,
    options: TestOptions
) -> ExecutionStrategy:
    # CLI override takes precedence
    if options.mode != "":
        return strategy_from_mode(options.mode, test_file)

    # Categorize test file
    val category = categorize_test_file(test_file)

    match category:
        "qemu":
            # QEMU needs container isolation
            ExecutionStrategy(
                mode: "container",
                profile: profile_intensive(),
                container_image: "simple-test-isolation:latest",
                container_runtime: "auto"
            )

        "baremetal":
            # Baremetal needs container isolation
            ExecutionStrategy(
                mode: "container",
                profile: profile_intensive(),
                container_image: "simple-test-isolation:latest",
                container_runtime: "auto"
            )

        "database":
            # Database tests need process isolation
            ExecutionStrategy(
                mode: "process",
                profile: profile_slow(),
                container_image: "",
                container_runtime: ""
            )

        "integration":
            # Integration tests use safe mode
            ExecutionStrategy(
                mode: "safe",
                profile: profile_standard(),
                container_image: "",
                container_runtime: ""
            )

        "unit":
            # Unit tests can run native (fast)
            ExecutionStrategy(
                mode: "native",
                profile: profile_fast(),
                container_image: "",
                container_runtime: ""
            )

        _:
            # Default: process isolation
            ExecutionStrategy(
                mode: "process",
                profile: profile_standard(),
                container_image: "",
                container_runtime: ""
            )

fn categorize_test_file(test_file: text) -> text:
    if test_file.contains("/qemu/"):
        return "qemu"
    if test_file.contains("/baremetal/"):
        return "baremetal"
    if test_file.contains("/database/") or test_file.contains("/lib/database/"):
        return "database"
    if test_file.contains("/integration/"):
        return "integration"
    if test_file.contains("/unit/"):
        return "unit"
    return "other"

fn strategy_from_mode(mode: text, test_file: text) -> ExecutionStrategy:
    # Manual mode selection (CLI override)
    match mode:
        "native":
            ExecutionStrategy(
                mode: "native",
                profile: profile_fast(),
                container_image: "",
                container_runtime: ""
            )
        "process":
            ExecutionStrategy(
                mode: "process",
                profile: profile_standard(),
                container_image: "",
                container_runtime: ""
            )
        "safe":
            ExecutionStrategy(
                mode: "safe",
                profile: profile_standard(),
                container_image: "",
                container_runtime: ""
            )
        "container":
            ExecutionStrategy(
                mode: "container",
                profile: profile_slow(),
                container_image: "simple-test-isolation:latest",
                container_runtime: "auto"
            )
        "container-seq":
            ExecutionStrategy(
                mode: "container_seq",
                profile: profile_intensive(),
                container_image: "simple-test-isolation:latest",
                container_runtime: "auto"
            )
        _:
            strategy_auto_select(test_file, TestOptions(mode: ""))

export ExecutionMode, ExecutionStrategy
export strategy_auto_select, categorize_test_file, strategy_from_mode
```

**Configuration Integration:**

Extend `simple.test.sdn`:

```sdn
test_config {
    # Execution strategy rules (file pattern matching)
    execution_rules [
        { pattern "test/integration/qemu/**" mode "container" profile "intensive" }
        { pattern "test/integration/baremetal/**" mode "container" profile "intensive" }
        { pattern "test/lib/database/**" mode "process" profile "slow" }
        { pattern "test/integration/**" mode "safe" profile "standard" }
        { pattern "test/unit/**" mode "native" profile "fast" }
    ]

    # Default execution mode (auto, native, process, safe, container)
    default_execution_mode "auto"

    # Container settings
    container_image "simple-test-isolation:latest"
    container_runtime "auto"  # auto, docker, podman
}
```

**Testing:**

Create `test/unit/app/test_runner_new/execution_strategy_spec.spl`:

```simple
use std.spec.{describe, it, expect}
use app.test_runner_new.execution_strategy.{
    strategy_auto_select,
    categorize_test_file,
    strategy_from_mode
}
use app.test_runner_new.test_runner_types.{TestOptions}

describe "execution_strategy":
    it "categorizes QEMU tests":
        val cat = categorize_test_file("test/integration/qemu/boot_spec.spl")
        expect(cat).to_equal("qemu")

    it "selects container mode for QEMU":
        val opts = TestOptions(mode: "")
        val strategy = strategy_auto_select("test/integration/qemu/boot_spec.spl", opts)
        expect(strategy.mode).to_equal("container")
        expect(strategy.profile.name).to_equal("intensive")

    it "selects process mode for database":
        val opts = TestOptions(mode: "")
        val strategy = strategy_auto_select("test/lib/database/query_spec.spl", opts)
        expect(strategy.mode).to_equal("process")

    it "selects native mode for unit tests":
        val opts = TestOptions(mode: "")
        val strategy = strategy_auto_select("test/unit/std/string_spec.spl", opts)
        expect(strategy.mode).to_equal("native")

    it "respects CLI override":
        val opts = TestOptions(mode: "container")
        val strategy = strategy_auto_select("test/unit/std/string_spec.spl", opts)
        expect(strategy.mode).to_equal("container")
```

**Success Criteria:**
- [ ] 5 execution modes defined (native, process, safe, container, container_seq)
- [ ] Auto-selection logic based on test file path
- [ ] Configuration file integration (simple.test.sdn)
- [ ] CLI mode override works (--mode=NAME)
- [ ] 20+ test cases validating strategy selection

**Files to Create:**
- `src/app/test_runner_new/execution_strategy.spl` - Strategy logic (NEW, ~300 lines)
- `test/unit/app/test_runner_new/execution_strategy_spec.spl` - Tests (NEW, ~120 lines)

**Files to Modify:**
- `simple.test.sdn` - Add execution_rules config (~30 lines)
- `src/app/test_runner_new/test_runner_args.spl` - Add --mode flag (~10 lines)

**Dependencies:** Phases 1, 2, 3

**Complexity:** Medium

---

### 4.2 Sequential Container Execution

**Objective:** Implement sequential container mode for maximum isolation (one container per test).

**File:** `src/app/test_runner_new/sequential_container.spl` (NEW, ~250 lines)

**Design:**

```simple
class SequentialContainerConfig:
    base_image: text
    runtime: text            # "docker" or "podman"
    memory_mb: i64
    cpu_cores: f64
    network: text            # "none" recommended
    cleanup_on_error: bool   # Delete container on failure

fn sequential_container_run_test(
    test_file: text,
    config: SequentialContainerConfig
) -> (TestFileResult, text):
    # Create unique container for this test
    val container_name = "simple-test-{random_id()}"

    # Create container (not started yet)
    val create_cmd = "{config.runtime} create " +
        "--name {container_name} " +
        "--memory={config.memory_mb}m " +
        "--cpus={config.cpu_cores} " +
        "--network={config.network} " +
        "--read-only " +
        "--tmpfs /tmp:rw,noexec,nosuid,size=100m " +
        "-v $(pwd):/workspace:ro " +
        "{config.base_image} " +
        "test {test_file}"

    val create_result = process_run(create_cmd)
    if not create_result.success:
        return (test_failure_result(test_file, "Container create failed"), "")

    # Start and wait for container
    val start_cmd = "{config.runtime} start -a {container_name}"
    val start_time = time_now_ms()
    val run_result = process_run(start_cmd)
    val duration = time_now_ms() - start_time

    # Get container logs (stdout/stderr)
    val logs_cmd = "{config.runtime} logs {container_name}"
    val logs_result = process_run(logs_cmd)

    # Parse test output
    val test_result = parse_test_output(logs_result.stdout, test_file)
    test_result.duration_ms = duration

    # Cleanup container
    val cleanup_cmd = "{config.runtime} rm {container_name}"
    process_run(cleanup_cmd)

    return (test_result, container_name)

fn sequential_container_run_all_tests(
    test_files: [text],
    config: SequentialContainerConfig
) -> [TestFileResult]:
    var results = []

    # Run tests sequentially (max isolation)
    for test_file in test_files:
        print "Running {test_file} in isolated container..."
        val (result, container_id) = sequential_container_run_test(test_file, config)
        results = results + [result]

        # Log result
        if result.status == "passed":
            print "  ✓ PASSED ({result.duration_ms}ms)"
        else:
            print "  ✗ FAILED: {result.error}"

    return results

fn random_id() -> text:
    # Generate random container ID (timestamp + random)
    val timestamp = time_now_ms()
    val random = timestamp % 100000
    return "{timestamp}-{random}"

export SequentialContainerConfig
export sequential_container_run_test, sequential_container_run_all_tests
```

**Integration with Test Runner:**

Update `src/app/test_runner_new/test_runner_main.spl`:

```simple
fn run_all_tests(test_files: [text], options: TestOptions) -> [TestFileResult]:
    # Detect execution mode
    if options.mode == "container-seq":
        # Sequential container mode (max isolation)
        val config = SequentialContainerConfig(
            base_image: "simple-test-isolation:latest",
            runtime: container_detect_engine(),
            memory_mb: 512,
            cpu_cores: 1.0,
            network: "none",
            cleanup_on_error: true
        )
        return sequential_container_run_all_tests(test_files, config)

    # Standard modes (native/process/safe/container)
    var results = []
    for test_file in test_files:
        val result = run_single_test(test_file, options)
        results = results + [result]
    return results
```

**CLI Flags:**

Add to `src/app/test_runner_new/test_runner_args.spl`:

```simple
# Execution mode flags
--mode=MODE                # Execution mode (auto, native, process, safe, container, container-seq)
--container-seq            # Alias for --mode=container-seq
--container-sequential     # Alias for --mode=container-seq
```

**Testing:**

Create `test/unit/app/test_runner_new/sequential_container_spec.spl`:

```simple
describe "sequential_container":
    it "runs test in isolated container":
        val config = SequentialContainerConfig(
            base_image: "simple-test-isolation:latest",
            runtime: "docker",
            memory_mb: 512,
            cpu_cores: 1.0,
            network: "none",
            cleanup_on_error: true
        )

        val (result, container_id) = sequential_container_run_test(
            "test/unit/std/string_spec.spl",
            config
        )

        expect(result.status).to_equal("passed")
        expect(container_id).to_contain("simple-test-")

    slow_it "runs multiple tests sequentially":
        val config = SequentialContainerConfig(
            base_image: "simple-test-isolation:latest",
            runtime: "docker",
            memory_mb: 512,
            cpu_cores: 1.0,
            network: "none",
            cleanup_on_error: true
        )

        val test_files = [
            "test/unit/std/string_spec.spl",
            "test/unit/std/array_spec.spl"
        ]

        val results = sequential_container_run_all_tests(test_files, config)

        expect(results.len()).to_equal(2)
        expect(results[0].status).to_equal("passed")
        expect(results[1].status).to_equal("passed")
```

**Success Criteria:**
- [ ] Sequential container execution works
- [ ] Each test gets fresh container
- [ ] Containers cleaned up after test
- [ ] Network isolation enforced (--network=none)
- [ ] Filesystem isolation (read-only + tmpfs)
- [ ] 15+ test cases validating sequential mode

**Files to Create:**
- `src/app/test_runner_new/sequential_container.spl` - Sequential logic (NEW, ~250 lines)
- `test/unit/app/test_runner_new/sequential_container_spec.spl` - Tests (NEW, ~80 lines)

**Files to Modify:**
- `src/app/test_runner_new/test_runner_main.spl` - Add sequential mode (~40 lines)
- `src/app/test_runner_new/test_runner_args.spl` - Add flags (~20 lines)

**Dependencies:** 4.1 complete

**Complexity:** Medium

---

## Phase 5: Long-Running Test Support & Production Hardening

**Duration:** 3-4 days
**Effort:** ~12-14 hours implementation + 6-7 hours testing
**Dependencies:** Phase 1-4 complete
**Risk:** Low
**Status:** NOT STARTED

### 5.1 Long-Running Test Profile

**Objective:** Add dedicated profile for tests with high resource needs (QEMU, compilation).

**File:** `src/std/process_limits.spl`

**Add Profile:**

```simple
fn profile_critical() -> ResourceProfile:
    ResourceProfile(
        name: "critical",
        cpu_ms: 3600000,     # 60 minutes (1 hour)
        mem_mb: 4096,        # 4 GB
        timeout_ms: 7200000, # 120 minutes (2 hours wall-clock)
        nice_level: 10,      # Lower priority
        max_files: 4096,
        max_procs: 512
    )

fn profile_from_name(name: text) -> ResourceProfile:
    match name:
        "fast": profile_fast()
        "standard": profile_standard()
        "slow": profile_slow()
        "intensive": profile_intensive()
        "critical": profile_critical()  # NEW
        _: profile_standard()
```

**Test Marker:**

Add to `src/std/spec.spl`:

```simple
fn critical_it(name: text, test_body: fn()):
    # Mark test as critical (long-running, resource-intensive)
    # NOTE: This is just a marker, actual enforcement in test runner
    it(name, test_body)
```

**Configuration:**

Update `simple.test.sdn`:

```sdn
test_config {
    profiles {
        critical {
            cpu_ms 3600000      # 1 hour CPU
            mem_mb 4096         # 4 GB
            timeout_ms 7200000  # 2 hours wall-clock
        }
    }

    # Tests requiring critical profile
    critical_tests [
        "test/integration/qemu/**"
        "test/integration/baremetal/**"
        "test/compiler/bootstrap/**"
        "test/system/self_hosting/**"
    ]
}
```

**Success Criteria:**
- [ ] Critical profile defined (1hr CPU, 4GB memory)
- [ ] critical_it() marker in spec.spl
- [ ] Configuration integration
- [ ] Test runner applies critical profile

**Files to Modify:**
- `src/std/process_limits.spl` - Add profile (~20 lines)
- `src/std/spec.spl` - Add critical_it (~10 lines)
- `simple.test.sdn` - Add critical config (~15 lines)

**Complexity:** Low

---

### 5.2 Resource Monitoring Integration

**Objective:** Integrate Phase 3 resource monitoring into test runner execution.

**File:** `src/app/test_runner_new/test_runner_execute.spl`

**Add Monitoring to Execution:**

```simple
fn run_test_file_with_monitoring(
    test_file: text,
    strategy: ExecutionStrategy,
    options: TestOptions
) -> (TestFileResult, ResourceUsageRecord):
    # Start test process asynchronously
    val binary = get_simple_binary()
    val args = build_test_args(test_file, options)
    val pid = process_spawn_async(binary, args)

    # Create resource monitor
    val limits = ResourceLimits(
        cpu_percent_limit: strategy.profile.cpu_ms / 1000.0 * 100.0,  # Convert to %
        memory_mb_limit: strategy.profile.mem_mb,
        fd_limit: strategy.profile.max_files,
        enabled: options.monitor_resources
    )

    # Monitor test execution
    val record = monitor_test_execution(pid, test_file, limits)

    # Wait for completion
    val exit_code = process_wait(pid, strategy.profile.timeout_ms)

    # Record to database
    if options.record_resources:
        record_test_resource_usage(test_file, record)

    # Check violations
    if has_violations(record):
        val alert = format_violation_alert(test_file, record)
        print alert

    # Build test result
    val result = TestFileResult(
        file_path: test_file,
        status: if exit_code == 0: "passed" else: "failed",
        error: "",
        duration_ms: record.duration_ms,
        tests_run: 1,
        tests_passed: if exit_code == 0: 1 else: 0,
        tests_failed: if exit_code == 0: 0 else: 1
    )

    return (result, record)
```

**CLI Flags:**

Add to `src/app/test_runner_new/test_runner_args.spl`:

```simple
# Resource monitoring flags
--monitor-resources        # Enable resource monitoring
--record-resources         # Record to database
--resource-report          # Generate report after tests
--no-monitor               # Disable monitoring (default)
```

**Update Main Loop:**

Modify `src/app/test_runner_new/test_runner_main.spl`:

```simple
fn run_all_tests(test_files: [text], options: TestOptions) -> [TestFileResult]:
    # ... existing code ...

    var all_resource_records = []

    for test_file in test_files:
        val strategy = strategy_auto_select(test_file, options)

        # Run with monitoring if enabled
        if options.monitor_resources:
            val (result, record) = run_test_file_with_monitoring(test_file, strategy, options)
            all_resource_records = all_resource_records + [record]
            results = results + [result]
        else:
            val result = run_single_test_with_strategy(test_file, strategy, options)
            results = results + [result]

    # Generate resource report if requested
    if options.resource_report and options.monitor_resources:
        val report = generate_resource_summary(20)  # Top 20
        file_write("doc/test/resource_usage_summary.md", report)
        print "\nResource report written to doc/test/resource_usage_summary.md"

    return results
```

**Success Criteria:**
- [ ] Resource monitoring integrated into test execution
- [ ] CLI flags for monitoring control
- [ ] Violations reported in real-time
- [ ] Database recording works
- [ ] Report generation at end of run

**Files to Modify:**
- `src/app/test_runner_new/test_runner_execute.spl` - Add monitoring (~80 lines)
- `src/app/test_runner_new/test_runner_main.spl` - Report generation (~40 lines)
- `src/app/test_runner_new/test_runner_args.spl` - Add flags (~20 lines)
- `test/unit/app/test_runner_new/test_runner_execute_spec.spl` - Tests (~60 lines)

**Dependencies:** Phase 3 complete

**Complexity:** Medium

---

## Implementation Timeline

### Week 1: Process Enforcement (Phase 1)
- **Day 1-2:** Implement process_run_with_limits() (~10 hours)
- **Day 3:** Integrate with test runner (~4 hours)
- **Day 4:** Testing and validation (~5 hours)

### Week 2: Hybrid Execution (Phase 4)
- **Day 1:** Execution strategy system (~6 hours)
- **Day 2:** Sequential container mode (~5 hours)
- **Day 3:** Unify execution modes (~5 hours)
- **Day 4:** Testing and validation (~6 hours)

### Week 3: Production Features (Phase 5)
- **Day 1:** Critical profile + monitoring integration (~6 hours)
- **Day 2:** Documentation (~5 hours)
- **Day 3:** End-to-end testing (~6 hours)

**Total:** ~53 hours (~2 weeks full-time)

---

## Success Metrics

### Overall Success Criteria

**Phase 1 (Process Enforcement):**
- [ ] process_run_with_limits() enforces CPU/memory limits (±10% accuracy)
- [ ] Limit violations detected and reported
- [ ] Safe mode uses enforced limits
- [ ] 25+ test cases passing
- [ ] No regressions in 4,067 existing tests

**Phase 4 (Hybrid Execution):**
- [ ] 5 execution modes working (native/process/safe/container/container-seq)
- [ ] Auto-selection based on test file path
- [ ] Sequential container mode provides max isolation
- [ ] Configuration file integration works
- [ ] 35+ test cases passing

**Phase 5 (Production):**
- [ ] Critical profile supports 1-hour tests
- [ ] Resource monitoring integrated
- [ ] Documentation complete
- [ ] 20+ test cases passing

### Performance Targets

- **Process mode overhead:** <5% vs native
- **Container mode overhead:** <10% vs native (already achieved)
- **Sequential container overhead:** ~50ms per test (container create/destroy)
- **Monitoring overhead:** <3% (already measured)

### Reliability Targets

- **Resource limit accuracy:** ±10% (ulimit enforcement)
- **Violation detection:** >95% accuracy
- **Container cleanup:** 100% (no orphaned containers)
- **Test isolation:** 100% (no state leakage between tests)

---

## Conclusion

This implementation plan consolidates existing work (Phases 2-3 complete) with new features (Phases 1, 4-5) to create a production-grade robust test runner for the Simple language.

**Key Achievements:**
- ✅ Container testing infrastructure (COMPLETE)
- ✅ Resource monitoring and tracking (COMPLETE)
- 🔲 Process resource enforcement (Phase 1, ~12 hours)
- 🔲 Hybrid execution strategy (Phase 4, ~16 hours)
- 🔲 Production hardening (Phase 5, ~12 hours)

**Total Remaining Work:** ~40 hours development + 17 hours testing = **57 hours** (~1.5 weeks full-time)

**Risk Level:** Low-Medium (mainly ulimit platform differences)

**Expected Outcome:**
- Enforced resource limits across all execution modes
- 5 execution modes (native → container-sequential)
- Production-grade isolation and monitoring
- Comprehensive documentation

**Status:** Ready to begin Phase 1 implementation.

---

**Report Completed:** 2026-02-14
**Total Pages:** 35+ (comprehensive implementation plan)
**Next Action:** Begin Phase 1.1 (process_run_with_limits implementation)
