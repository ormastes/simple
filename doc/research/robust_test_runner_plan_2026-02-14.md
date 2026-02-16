# Robust Test Runner Implementation Plan

**Date:** 2026-02-14
**Status:** Research & Planning
**Goal:** Production-grade test infrastructure with process isolation, resource limits, and containerization

---

## Executive Summary

Transform the Simple Language test runner from a fast, functional system (4,067 tests, 17.4s, 100% passing) into a production-grade testing platform with robust isolation, resource management, and scalability.

**Current State:**
- File-level subprocess isolation via `process_run_timeout()`
- Safe mode with hardcoded limits (512MB, 30s CPU)
- Resource limits NOT enforced except timeout
- 20,988+ slow_it markers indicating resource-intensive tests
- Temp file cleanup issues in /tmp/test_*.sdn

**Target State:**
- Per-test process isolation with enforced CPU/memory limits
- Container-based isolation for critical tests (QEMU, baremetal, database)
- Configurable resource profiles (fast, standard, slow, intensive)
- Distributed execution support for CI/CD
- Production-grade monitoring and diagnostics

---

## Phase 1: Foundation - Process Limits Enhancement

**Duration:** 2-3 days
**Effort:** ~8-12 hours implementation + 4-6 hours testing
**Dependencies:** None
**Risk:** Low

### 1.1 Implement Real process_run_with_limits()

**File:** `src/app/io/mod.spl`

**Current Implementation:**
```simple
fn process_run_with_limits(cmd: text, cpu_ms: i64, mem_mb: i64) -> ProcessResult:
    print "WARNING: Resource limits not enforced - falling back to process_run()"
    process_run(cmd)
```

**New Implementation Strategy:**

```simple
fn process_run_with_limits(cmd: text, cpu_ms: i64, mem_mb: i64) -> ProcessResult:
    # Build ulimit wrapper command
    val timeout_sec = cpu_ms / 1000
    val mem_kb = mem_mb * 1024

    # ulimit -v: virtual memory (KB)
    # ulimit -t: CPU time (seconds)
    # timeout: wall-clock time with buffer
    val wrapped_cmd = "ulimit -v {mem_kb}; ulimit -t {timeout_sec}; timeout {timeout_sec + 5}s {cmd}"

    val result = process_run(wrapped_cmd)

    # Detect limit violations
    var limit_exceeded = false
    var limit_type = ""

    if result.exit_code == 137:  # SIGKILL from timeout
        limit_exceeded = true
        limit_type = "timeout"
    if result.exit_code == 139:  # SIGSEGV from memory
        limit_exceeded = true
        limit_type = "memory"
    if result.stderr.contains("CPU time limit exceeded"):
        limit_exceeded = true
        limit_type = "cpu"

    # Return enhanced result
    ProcessResult(
        exit_code: result.exit_code,
        stdout: result.stdout,
        stderr: result.stderr,
        success: result.success,
        limit_exceeded: limit_exceeded,
        limit_type: limit_type
    )
```

**Changes Required:**

1. **Update ProcessResult struct** (`src/app/io/mod.spl`):
   ```simple
   class ProcessResult:
       exit_code: i64
       stdout: text
       stderr: text
       success: bool
       limit_exceeded: bool    # NEW
       limit_type: text        # NEW: "timeout", "cpu", "memory", ""
   ```

2. **Add helper functions**:
   ```simple
   fn format_ulimit_command(cpu_sec: i64, mem_kb: i64, cmd: text) -> text:
       "ulimit -v {mem_kb}; ulimit -t {cpu_sec}; {cmd}"

   fn parse_limit_violation(exit_code: i64, stderr: text) -> (bool, text):
       # Returns (violated, type)
       # Exit codes: 137=SIGKILL, 139=SIGSEGV, 159=timeout
       pass_todo
   ```

3. **Fallback for non-Unix platforms**:
   ```simple
   fn process_run_with_limits(cmd: text, cpu_ms: i64, mem_mb: i64) -> ProcessResult:
       if is_windows():
           print "WARNING: Resource limits not supported on Windows"
           return process_run(cmd)

       # Unix implementation...
   ```

**Testing:**

Create `test/unit/app/io/process_limits_spec.spl`:
```simple
use std.spec.{describe, it, expect}
use app.io.mod.{process_run_with_limits}

describe "process_run_with_limits":
    it "enforces CPU time limit":
        val result = process_run_with_limits(
            "bash -c 'while true; do :; done'",
            cpu_ms: 1000,
            mem_mb: 100
        )
        expect(result.limit_exceeded).to_equal(true)
        expect(result.limit_type).to_equal("cpu")

    it "enforces memory limit":
        val result = process_run_with_limits(
            "python3 -c 'x = [0] * 10**9'",
            cpu_ms: 30000,
            mem_mb: 50
        )
        expect(result.limit_exceeded).to_equal(true)
        expect(result.limit_type).to_equal("memory")

    it "succeeds within limits":
        val result = process_run_with_limits(
            "echo 'hello'",
            cpu_ms: 5000,
            mem_mb: 100
        )
        expect(result.success).to_equal(true)
        expect(result.limit_exceeded).to_equal(false)
```

**Success Criteria:**
- [ ] ProcessResult struct extended with limit tracking fields
- [ ] process_run_with_limits() enforces CPU limits (±10% accuracy)
- [ ] process_run_with_limits() enforces memory limits (±10% accuracy)
- [ ] Limit violations correctly detected and reported
- [ ] 15+ test cases passing (CPU, memory, timeout, success cases)
- [ ] Windows fallback gracefully degrades

---

### 1.2 Resource Profile System

**File:** `src/app/test_runner_new/resource_profiles.spl` (NEW, ~200 lines)

**Design:**

```simple
# Resource profile definitions
class ResourceProfile:
    name: text
    cpu_ms: i64          # CPU time limit
    mem_mb: i64          # Memory limit
    timeout_ms: i64      # Wall-clock timeout
    nice_level: i64      # Process priority (-20 to 19)
    max_files: i64       # File descriptor limit
    max_procs: i64       # Process count limit

fn profile_fast() -> ResourceProfile:
    ResourceProfile(
        name: "fast",
        cpu_ms: 1000,        # 1 second
        mem_mb: 128,
        timeout_ms: 2000,
        nice_level: 0,
        max_files: 100,
        max_procs: 10
    )

fn profile_standard() -> ResourceProfile:
    ResourceProfile(
        name: "standard",
        cpu_ms: 5000,        # 5 seconds
        mem_mb: 512,
        timeout_ms: 10000,
        nice_level: 0,
        max_files: 500,
        max_procs: 50
    )

fn profile_slow() -> ResourceProfile:
    ResourceProfile(
        name: "slow",
        cpu_ms: 30000,       # 30 seconds
        mem_mb: 1024,
        timeout_ms: 60000,
        nice_level: 5,
        max_files: 1000,
        max_procs: 100
    )

fn profile_intensive() -> ResourceProfile:
    ResourceProfile(
        name: "intensive",
        cpu_ms: 120000,      # 2 minutes
        mem_mb: 4096,
        timeout_ms: 300000,  # 5 minutes
        nice_level: 10,
        max_files: 2000,
        max_procs: 200
    )

fn profile_from_name(name: text) -> ResourceProfile:
    match name:
        "fast": profile_fast()
        "standard": profile_standard()
        "slow": profile_slow()
        "intensive": profile_intensive()
        _: profile_standard()  # Default

fn profile_from_test_markers(markers: [text]) -> ResourceProfile:
    # Detect resource profile from test markers
    if markers.contains("slow_it"):
        return profile_slow()
    if markers.contains("intensive"):
        return profile_intensive()
    if markers.contains("fast"):
        return profile_fast()
    return profile_standard()

export profile_fast, profile_standard, profile_slow, profile_intensive
export profile_from_name, profile_from_test_markers
export ResourceProfile
```

**Configuration Integration:**

Extend `simple.test.sdn`:
```sdn
test_config {
    # Resource profiles
    profiles {
        fast {
            cpu_ms 1000
            mem_mb 128
            timeout_ms 2000
        }
        standard {
            cpu_ms 5000
            mem_mb 512
            timeout_ms 10000
        }
        slow {
            cpu_ms 30000
            mem_mb 1024
            timeout_ms 60000
        }
        intensive {
            cpu_ms 120000
            mem_mb 4096
            timeout_ms 300000
        }
    }

    # Default profile per category
    default_profile "standard"
    slow_it_profile "slow"

    # Override per test file pattern
    file_profiles [
        { pattern "test/integration/qemu/**" profile "intensive" }
        { pattern "test/unit/**" profile "fast" }
    ]
}
```

**Testing:**

Create `test/unit/app/test_runner_new/resource_profiles_spec.spl`:
```simple
describe "ResourceProfile":
    it "creates fast profile":
        val prof = profile_fast()
        expect(prof.cpu_ms).to_equal(1000)
        expect(prof.mem_mb).to_equal(128)

    it "selects profile from markers":
        val prof = profile_from_test_markers(["slow_it"])
        expect(prof.name).to_equal("slow")
```

**Success Criteria:**
- [ ] 4 resource profiles defined (fast, standard, slow, intensive)
- [ ] Profile selection from test markers
- [ ] Configuration file integration (simple.test.sdn)
- [ ] Profile override per test file pattern
- [ ] 20+ test cases validating profile behavior

---

### 1.3 Integrate Profiles into Test Runner

**File:** `src/app/test_runner_new/test_runner_main.spl`

**Changes:**

1. **Import resource profiles**:
   ```simple
   use app.test_runner_new.resource_profiles.{
       ResourceProfile,
       profile_from_test_markers,
       profile_from_name
   }
   ```

2. **Update run_single_test()** (~line 150):
   ```simple
   fn run_single_test(test_file: text, test_config: TestConfig) -> TestResult:
       # Detect resource profile
       val markers = extract_test_markers(test_file)  # NEW helper
       val profile = profile_from_test_markers(markers)

       # Build command with resource limits
       val test_cmd = "bin/simple test {test_file}"

       val result = process_run_with_limits(
           test_cmd,
           cpu_ms: profile.cpu_ms,
           mem_mb: profile.mem_mb
       )

       # Check for limit violations
       if result.limit_exceeded:
           return TestResult(
               file: test_file,
               status: "failed",
               error: "Resource limit exceeded: {profile.limit_type}",
               duration_ms: profile.timeout_ms
           )

       # Parse test output...
   ```

3. **Add marker extraction helper**:
   ```simple
   fn extract_test_markers(test_file: text) -> [text]:
       val content = file_read(test_file)
       var markers = []

       # Look for slow_it, intensive, fast markers
       if content.contains("slow_it"):
           markers = markers + ["slow_it"]
       if content.contains("# @intensive"):
           markers = markers + ["intensive"]
       if content.contains("# @fast"):
           markers = markers + ["fast"]

       return markers
   ```

**Testing:**

Update `test/unit/app/test_runner_new/test_runner_spec.spl`:
```simple
describe "run_single_test with resource profiles":
    it "applies slow profile to slow_it tests":
        val config = default_test_config()
        val result = run_single_test(
            "test/fixtures/slow_test_spec.spl",
            config
        )
        # Verify slow profile was used
        expect(result.status).to_equal("passed")

    it "detects CPU limit violations":
        val result = run_single_test(
            "test/fixtures/cpu_intensive_spec.spl",
            config
        )
        expect(result.status).to_equal("failed")
        expect(result.error).to_contain("Resource limit exceeded: cpu")
```

**Success Criteria:**
- [ ] Test runner applies profiles based on markers
- [ ] Resource violations reported in test results
- [ ] CLI flag `--profile=NAME` overrides detection
- [ ] 10+ integration tests validating profile enforcement
- [ ] Existing 4,067 tests still pass (no regressions)

---

## Phase 2: Container Integration

**Duration:** 4-5 days
**Effort:** ~16-20 hours implementation + 8-10 hours testing
**Dependencies:** Phase 1 complete
**Risk:** Medium

### 2.1 Docker Image for Test Execution

**File:** `docker/test-runner.Dockerfile` (NEW)

**Dockerfile:**

```dockerfile
FROM alpine:3.19

# Install runtime dependencies
RUN apk add --no-cache \
    bash \
    coreutils \
    findutils \
    ncurses \
    libstdc++

# Create test user (non-root)
RUN addgroup -g 1000 testuser && \
    adduser -D -u 1000 -G testuser testuser

# Copy Simple runtime
COPY bin/release/simple /usr/local/bin/simple
RUN chmod +x /usr/local/bin/simple

# Create workspace
WORKDIR /workspace
RUN chown testuser:testuser /workspace

# Switch to non-root user
USER testuser

# Default command
ENTRYPOINT ["/usr/local/bin/simple"]
CMD ["test"]
```

**Build Script:** `scripts/docker-build-test-runner.sh`

```bash
#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

cd "$PROJECT_ROOT"

# Ensure runtime exists
if [ ! -f "bin/release/simple" ]; then
    echo "ERROR: bin/release/simple not found. Run: bin/simple build --release"
    exit 1
fi

# Build image
docker build \
    -f docker/test-runner.Dockerfile \
    -t simple-test-runner:latest \
    -t simple-test-runner:$(date +%Y%m%d) \
    .

echo "Built image: simple-test-runner:latest"
docker images simple-test-runner
```

**Testing:**

```bash
# Build image
./scripts/docker-build-test-runner.sh

# Run single test
docker run --rm \
    -v $(pwd):/workspace:ro \
    --memory=512m \
    --cpus=1.0 \
    simple-test-runner:latest \
    test test/unit/std/string_spec.spl

# Run full suite
docker run --rm \
    -v $(pwd):/workspace:ro \
    --memory=2g \
    --cpus=4.0 \
    simple-test-runner:latest \
    test
```

**Success Criteria:**
- [ ] Dockerfile builds successfully (<5 min)
- [ ] Image size <50MB
- [ ] Single test execution works in container
- [ ] Full test suite runs in container (4,067 tests pass)
- [ ] Resource limits enforced by Docker (memory, CPU)

---

### 2.2 Container Execution Backend

**File:** `src/app/test_runner_new/container_backend.spl` (NEW, ~300 lines)

**Design:**

```simple
class ContainerConfig:
    engine: text           # "docker" or "podman"
    image: text            # "simple-test-runner:latest"
    memory_mb: i64
    cpu_count: f64
    network: text          # "none", "bridge", "host"
    readonly: bool         # Mount workspace read-only
    temp_dir: text         # Temp directory for output

class ContainerResult:
    exit_code: i64
    stdout: text
    stderr: text
    success: bool
    duration_ms: i64
    container_id: text
    resource_stats: text   # Docker stats output

fn container_run_test(
    test_file: text,
    config: ContainerConfig
) -> ContainerResult:
    # Build docker run command
    val mount_flag = if config.readonly: "ro" else: "rw"
    val workspace = "$(pwd)"

    val cmd = "docker run --rm " +
        "--memory={config.memory_mb}m " +
        "--cpus={config.cpu_count} " +
        "--network={config.network} " +
        "-v {workspace}:/workspace:{mount_flag} " +
        "{config.image} " +
        "test {test_file}"

    val start_time = time_now_ms()
    val result = process_run(cmd)
    val duration = time_now_ms() - start_time

    ContainerResult(
        exit_code: result.exit_code,
        stdout: result.stdout,
        stderr: result.stderr,
        success: result.success,
        duration_ms: duration,
        container_id: "",
        resource_stats: ""
    )

fn container_detect_engine() -> text:
    # Try docker first
    val docker_check = process_run("docker --version")
    if docker_check.success:
        return "docker"

    # Try podman
    val podman_check = process_run("podman --version")
    if podman_check.success:
        return "podman"

    return "none"

fn container_create_config(profile: ResourceProfile) -> ContainerConfig:
    ContainerConfig(
        engine: container_detect_engine(),
        image: "simple-test-runner:latest",
        memory_mb: profile.mem_mb,
        cpu_count: profile.cpu_ms / 1000.0,  # Rough conversion
        network: "none",
        readonly: true,
        temp_dir: "/tmp/simple-test"
    )

export ContainerConfig, ContainerResult
export container_run_test, container_detect_engine
export container_create_config
```

**CLI Integration:**

Add flags to `src/app/cli/main.spl`:
```simple
# Test command flags
--container         # Use container backend
--container-image   # Override default image
--container-engine  # Force docker/podman
```

**Testing:**

Create `test/unit/app/test_runner_new/container_backend_spec.spl`:
```simple
describe "container_backend":
    it "detects docker engine":
        val engine = container_detect_engine()
        expect(engine).to_equal("docker")

    it "runs test in container":
        val config = ContainerConfig(
            engine: "docker",
            image: "simple-test-runner:latest",
            memory_mb: 512,
            cpu_count: 1.0,
            network: "none",
            readonly: true,
            temp_dir: "/tmp/test"
        )

        val result = container_run_test(
            "test/unit/std/string_spec.spl",
            config
        )

        expect(result.success).to_equal(true)
        expect(result.exit_code).to_equal(0)
```

**Success Criteria:**
- [ ] Container engine auto-detection (docker/podman)
- [ ] Single test execution in container
- [ ] Resource limits applied via Docker flags
- [ ] Test output captured correctly
- [ ] 15+ test cases validating container execution
- [ ] CLI flags work (`--container`, `--container-image`)

---

### 2.3 Hybrid Execution Strategy

**File:** `src/app/test_runner_new/execution_strategy.spl` (NEW, ~250 lines)

**Design:**

```simple
enum ExecutionMode:
    Native           # Direct process execution
    Process          # Process with ulimit
    Container        # Docker/Podman isolation

class ExecutionStrategy:
    mode: text               # "native", "process", "container"
    profile: ResourceProfile
    container_config: ContainerConfig?

fn strategy_from_test_file(
    test_file: text,
    config: TestConfig
) -> ExecutionStrategy:
    # Categorize test file
    val category = categorize_test_file(test_file)

    match category:
        "qemu":
            # QEMU tests need full container isolation
            ExecutionStrategy(
                mode: "container",
                profile: profile_intensive(),
                container_config: container_create_config(profile_intensive())
            )

        "database":
            # Database tests need process isolation
            ExecutionStrategy(
                mode: "process",
                profile: profile_slow(),
                container_config: nil
            )

        "unit":
            # Unit tests can run native
            ExecutionStrategy(
                mode: "native",
                profile: profile_fast(),
                container_config: nil
            )

        _:
            # Default: process isolation
            ExecutionStrategy(
                mode: "process",
                profile: profile_standard(),
                container_config: nil
            )

fn categorize_test_file(test_file: text) -> text:
    if test_file.contains("/qemu/"):
        return "qemu"
    if test_file.contains("/baremetal/"):
        return "baremetal"
    if test_file.contains("/database/"):
        return "database"
    if test_file.contains("/integration/"):
        return "integration"
    if test_file.contains("/unit/"):
        return "unit"
    return "other"

fn execute_test_with_strategy(
    test_file: text,
    strategy: ExecutionStrategy
) -> TestResult:
    match strategy.mode:
        "native":
            execute_test_native(test_file)

        "process":
            execute_test_process(test_file, strategy.profile)

        "container":
            val container_cfg = strategy.container_config ?? container_create_config(strategy.profile)
            execute_test_container(test_file, container_cfg)

        _:
            execute_test_native(test_file)

export ExecutionMode, ExecutionStrategy
export strategy_from_test_file, execute_test_with_strategy
```

**Configuration:**

Extend `simple.test.sdn`:
```sdn
test_config {
    # Execution strategy rules
    execution_rules [
        { pattern "test/integration/qemu/**" mode "container" profile "intensive" }
        { pattern "test/integration/baremetal/**" mode "container" profile "intensive" }
        { pattern "test/lib/database/**" mode "process" profile "slow" }
        { pattern "test/unit/**" mode "native" profile "fast" }
    ]

    # Fallback mode
    default_mode "process"
}
```

**Testing:**

Create `test/unit/app/test_runner_new/execution_strategy_spec.spl`:
```simple
describe "execution_strategy":
    it "selects container mode for QEMU tests":
        val strategy = strategy_from_test_file(
            "test/integration/qemu/boot_spec.spl",
            default_test_config()
        )
        expect(strategy.mode).to_equal("container")
        expect(strategy.profile.name).to_equal("intensive")

    it "selects process mode for database tests":
        val strategy = strategy_from_test_file(
            "test/lib/database/query_spec.spl",
            default_test_config()
        )
        expect(strategy.mode).to_equal("process")

    it "selects native mode for unit tests":
        val strategy = strategy_from_test_file(
            "test/unit/std/string_spec.spl",
            default_test_config()
        )
        expect(strategy.mode).to_equal("native")
```

**Success Criteria:**
- [ ] Test categorization logic (qemu, database, unit, etc.)
- [ ] Execution mode selection based on category
- [ ] Configuration file integration
- [ ] CLI override flags (`--force-mode=container`)
- [ ] 25+ test cases validating strategy selection
- [ ] Full test suite runs with hybrid strategy (0 regressions)

---

## Phase 3: Resource Enforcement & Monitoring

**Duration:** 3-4 days
**Effort:** ~12-16 hours implementation + 6-8 hours testing
**Dependencies:** Phase 1, Phase 2 complete
**Risk:** Medium

### 3.1 Real-Time Resource Monitoring

**File:** `src/app/test_runner_new/resource_monitor.spl` (NEW, ~400 lines)

**Design:**

```simple
class ResourceSnapshot:
    timestamp_ms: i64
    cpu_percent: f64
    memory_mb: i64
    file_descriptors: i64
    thread_count: i64

class ResourceMonitor:
    pid: i64
    interval_ms: i64
    snapshots: [ResourceSnapshot]

fn monitor_create(pid: i64, interval_ms: i64) -> ResourceMonitor:
    ResourceMonitor(
        pid: pid,
        interval_ms: interval_ms,
        snapshots: []
    )

fn monitor_start(monitor: ResourceMonitor):
    # Start background monitoring thread
    # Read /proc/{pid}/stat, /proc/{pid}/status periodically
    # Store snapshots for later analysis
    pass_todo

fn monitor_stop(monitor: ResourceMonitor) -> [ResourceSnapshot]:
    # Stop monitoring thread
    # Return collected snapshots
    return monitor.snapshots

fn monitor_analyze(snapshots: [ResourceSnapshot]) -> ResourceStats:
    # Compute statistics
    var max_cpu = 0.0
    var max_mem = 0
    var avg_cpu = 0.0

    # Calculate max, avg, p95, p99
    pass_todo

class ResourceStats:
    max_cpu_percent: f64
    max_memory_mb: i64
    avg_cpu_percent: f64
    avg_memory_mb: i64
    p95_cpu_percent: f64
    p95_memory_mb: i64
    p99_cpu_percent: f64
    p99_memory_mb: i64
    samples: i64

export ResourceSnapshot, ResourceMonitor, ResourceStats
export monitor_create, monitor_start, monitor_stop, monitor_analyze
```

**Linux /proc Integration:**

```simple
fn read_proc_stat(pid: i64) -> ResourceSnapshot:
    val stat_file = "/proc/{pid}/stat"
    val content = file_read(stat_file)

    # Parse stat file (space-separated)
    val parts = content.split(" ")

    # Extract fields (see proc(5) man page)
    val utime = int(parts[13])   # User CPU time
    val stime = int(parts[14])   # System CPU time
    val rss = int(parts[23])     # Resident set size

    # Calculate CPU percentage
    val total_time = utime + stime
    val cpu_percent = total_time / 100.0  # Simplified

    ResourceSnapshot(
        timestamp_ms: time_now_ms(),
        cpu_percent: cpu_percent,
        memory_mb: rss / 1024,
        file_descriptors: count_file_descriptors(pid),
        thread_count: count_threads(pid)
    )

fn count_file_descriptors(pid: i64) -> i64:
    val fd_dir = "/proc/{pid}/fd"
    val entries = dir_list(fd_dir)
    return entries.len()

fn count_threads(pid: i64) -> i64:
    val task_dir = "/proc/{pid}/task"
    val entries = dir_list(task_dir)
    return entries.len()
```

**Integration with Test Runner:**

```simple
fn run_single_test_monitored(
    test_file: text,
    config: TestConfig
) -> (TestResult, ResourceStats):
    # Start test process
    val pid = process_spawn_async(test_cmd)

    # Start monitoring
    val monitor = monitor_create(pid, interval_ms: 100)
    monitor_start(monitor)

    # Wait for completion
    val result = process_wait(pid)

    # Stop monitoring
    val snapshots = monitor_stop(monitor)
    val stats = monitor_analyze(snapshots)

    return (result, stats)
```

**Testing:**

Create `test/unit/app/test_runner_new/resource_monitor_spec.spl`:
```simple
describe "resource_monitor":
    it "captures CPU usage":
        val pid = process_spawn_async("stress --cpu 1 --timeout 2s")
        val monitor = monitor_create(pid, 100)
        monitor_start(monitor)
        process_wait(pid)
        val snapshots = monitor_stop(monitor)

        expect(snapshots.len()).to_be_greater_than(10)
        val stats = monitor_analyze(snapshots)
        expect(stats.max_cpu_percent).to_be_greater_than(50.0)

    it "captures memory usage":
        # Test with memory-intensive process
        pass_todo
```

**Success Criteria:**
- [ ] ResourceMonitor captures CPU/memory snapshots
- [ ] /proc filesystem integration works
- [ ] Statistics computed correctly (max, avg, p95, p99)
- [ ] Monitoring thread doesn't affect test performance (<5% overhead)
- [ ] 20+ test cases validating monitoring accuracy

---

### 3.2 Resource Violation Detection & Reporting

**File:** `src/app/test_runner_new/violation_detector.spl` (NEW, ~250 lines)

**Design:**

```simple
enum ViolationType:
    CpuExceeded
    MemoryExceeded
    TimeoutExceeded
    FileDescriptorLeak
    ThreadLeak

class ResourceViolation:
    type: text               # "cpu", "memory", "timeout", etc.
    threshold: f64           # Expected limit
    actual: f64              # Actual value
    severity: text           # "warning", "error", "critical"
    message: text

fn detect_violations(
    stats: ResourceStats,
    profile: ResourceProfile
) -> [ResourceViolation]:
    var violations = []

    # CPU violation
    if stats.max_cpu_percent > profile.cpu_ms / 10.0:  # Simplified
        violations = violations + [ResourceViolation(
            type: "cpu",
            threshold: profile.cpu_ms / 10.0,
            actual: stats.max_cpu_percent,
            severity: "error",
            message: "CPU usage exceeded: {stats.max_cpu_percent}% > {profile.cpu_ms / 10.0}%"
        )]

    # Memory violation
    if stats.max_memory_mb > profile.mem_mb:
        violations = violations + [ResourceViolation(
            type: "memory",
            threshold: profile.mem_mb,
            actual: stats.max_memory_mb,
            severity: "error",
            message: "Memory usage exceeded: {stats.max_memory_mb}MB > {profile.mem_mb}MB"
        )]

    return violations

fn format_violation_report(violations: [ResourceViolation]) -> text:
    if violations.len() == 0:
        return "No resource violations detected"

    var report = "RESOURCE VIOLATIONS DETECTED:\n"

    for violation in violations:
        report = report + "  [{violation.severity}] {violation.message}\n"

    return report

export ViolationType, ResourceViolation
export detect_violations, format_violation_report
```

**Test Result Enhancement:**

Update `TestResult` struct to include violations:
```simple
class TestResult:
    file: text
    status: text
    error: text
    duration_ms: i64
    resource_stats: ResourceStats?      # NEW
    violations: [ResourceViolation]     # NEW
```

**Testing:**

```simple
describe "violation_detector":
    it "detects CPU violations":
        val stats = ResourceStats(
            max_cpu_percent: 150.0,
            max_memory_mb: 100,
            # ... other fields
        )
        val profile = profile_standard()
        val violations = detect_violations(stats, profile)

        expect(violations.len()).to_be_greater_than(0)
        expect(violations[0].type).to_equal("cpu")

    it "formats violation report":
        val violation = ResourceViolation(
            type: "memory",
            threshold: 512.0,
            actual: 1024.0,
            severity: "error",
            message: "Memory exceeded"
        )
        val report = format_violation_report([violation])
        expect(report).to_contain("RESOURCE VIOLATIONS")
```

**Success Criteria:**
- [ ] Violation detection for CPU, memory, timeout
- [ ] File descriptor leak detection
- [ ] Thread leak detection
- [ ] Formatted violation reports
- [ ] Integration with test runner output
- [ ] 15+ test cases validating detection logic

---

### 3.3 Resource Usage Database

**File:** `src/lib/database/resource_db.spl` (NEW, ~300 lines)

**Schema:**

```simple
class TestResourceRecord:
    test_file: text
    timestamp: i64
    duration_ms: i64
    max_cpu_percent: f64
    max_memory_mb: i64
    avg_cpu_percent: f64
    avg_memory_mb: i64
    violations: text         # JSON array of violations
    profile_used: text
    execution_mode: text

fn resource_db_init():
    # Initialize database in doc/test/resource_usage.sdn
    pass_todo

fn resource_db_record(
    test_file: text,
    stats: ResourceStats,
    violations: [ResourceViolation],
    profile: ResourceProfile,
    mode: text
):
    val record = TestResourceRecord(
        test_file: test_file,
        timestamp: time_now_ms(),
        duration_ms: 0,  # TODO
        max_cpu_percent: stats.max_cpu_percent,
        max_memory_mb: stats.max_memory_mb,
        avg_cpu_percent: stats.avg_cpu_percent,
        avg_memory_mb: stats.avg_memory_mb,
        violations: format_violations_json(violations),
        profile_used: profile.name,
        execution_mode: mode
    )

    # Append to database
    pass_todo

fn resource_db_query_worst_offenders(limit: i64) -> [TestResourceRecord]:
    # Query top N tests by max_memory_mb or max_cpu_percent
    pass_todo

fn resource_db_generate_report() -> text:
    # Generate markdown report with:
    # - Top 10 CPU consumers
    # - Top 10 memory consumers
    # - Tests with most violations
    # - Resource trends over time
    pass_todo
```

**Report Generation:**

Create `doc/test/resource_usage.md` automatically:
```markdown
# Test Resource Usage Report

**Generated:** 2026-02-14 15:30:00
**Total Tests:** 4,067
**Tests Monitored:** 4,067

## Top CPU Consumers

| Test File | Max CPU % | Avg CPU % | Profile |
|-----------|-----------|-----------|---------|
| test/integration/qemu/boot_spec.spl | 195.3% | 87.2% | intensive |
| test/compiler/backend/optimizer_spec.spl | 178.1% | 65.4% | slow |
| ... | ... | ... | ... |

## Top Memory Consumers

| Test File | Max Memory (MB) | Avg Memory (MB) | Profile |
|-----------|-----------------|-----------------|---------|
| test/lib/database/bulk_insert_spec.spl | 2,048 | 1,024 | slow |
| test/integration/compiler/large_file_spec.spl | 1,536 | 768 | slow |
| ... | ... | ... | ... |

## Violation Summary

- **Total Violations:** 127
- **CPU Violations:** 45
- **Memory Violations:** 67
- **Timeout Violations:** 15

## Resource Trends

(Graph showing resource usage over last 7 days)
```

**Success Criteria:**
- [ ] Database schema defined
- [ ] Record insertion works
- [ ] Query functions implemented
- [ ] Report generation produces markdown
- [ ] Historical trend tracking (7+ days)

---

## Phase 4: Advanced Isolation

**Duration:** 5-6 days
**Effort:** ~20-24 hours implementation + 10-12 hours testing
**Dependencies:** Phase 2, Phase 3 complete
**Risk:** High

### 4.1 Per-Test Container Isolation

**File:** `src/app/test_runner_new/per_test_container.spl` (NEW, ~350 lines)

**Design:**

```simple
class PerTestContainerConfig:
    base_image: text
    test_file: text
    resource_profile: ResourceProfile
    isolation_level: text    # "standard", "strict", "paranoid"
    network_mode: text       # "none", "isolated", "bridge"
    filesystem_mode: text    # "readonly", "tmpfs", "overlay"

fn container_run_isolated_test(
    test_file: text,
    config: PerTestContainerConfig
) -> ContainerResult:
    # Create isolated container for single test
    val container_id = container_create_isolated(config)

    # Copy test file into container
    container_copy_file(container_id, test_file, "/test.spl")

    # Run test
    val result = container_exec(container_id, "simple test /test.spl")

    # Cleanup
    container_remove(container_id)

    return result

fn container_create_isolated(config: PerTestContainerConfig) -> text:
    # Create container with:
    # - Unique temp directory
    # - No network (--network=none)
    # - Read-only filesystem (--read-only)
    # - tmpfs for /tmp
    # - Resource limits

    val create_cmd = "docker create " +
        "--name test-{random_id()} " +
        "--network={config.network_mode} " +
        "--read-only " +
        "--tmpfs /tmp:rw,noexec,nosuid,size=100m " +
        "--memory={config.resource_profile.mem_mb}m " +
        "--cpus={config.resource_profile.cpu_ms / 1000.0} " +
        "{config.base_image}"

    val result = process_run(create_cmd)
    return result.stdout.trim()  # Container ID
```

**Isolation Levels:**

```simple
fn isolation_standard() -> PerTestContainerConfig:
    # Standard isolation: read-only FS, no network, shared /tmp
    pass_todo

fn isolation_strict() -> PerTestContainerConfig:
    # Strict isolation: + tmpfs /tmp, no shared volumes
    pass_todo

fn isolation_paranoid() -> PerTestContainerConfig:
    # Paranoid isolation: + seccomp, apparmor, dropped capabilities
    pass_todo
```

**Security Enhancements:**

Add seccomp profile (`docker/seccomp-test-profile.json`):
```json
{
  "defaultAction": "SCMP_ACT_ALLOW",
  "syscalls": [
    {
      "name": "unshare",
      "action": "SCMP_ACT_ERRNO"
    },
    {
      "name": "mount",
      "action": "SCMP_ACT_ERRNO"
    }
  ]
}
```

**Testing:**

```simple
describe "per_test_container":
    it "isolates test in container":
        val config = isolation_standard()
        val result = container_run_isolated_test(
            "test/unit/std/string_spec.spl",
            config
        )
        expect(result.success).to_equal(true)

    it "prevents network access":
        val config = isolation_strict()
        val result = container_run_isolated_test(
            "test/fixtures/network_test_spec.spl",
            config
        )
        # Should fail due to network disabled
        expect(result.success).to_equal(false)
```

**Success Criteria:**
- [ ] Per-test container creation/destruction
- [ ] Three isolation levels implemented
- [ ] Network isolation enforced
- [ ] Filesystem isolation (read-only + tmpfs)
- [ ] Security profiles applied (seccomp, apparmor)
- [ ] 30+ test cases validating isolation
- [ ] Performance acceptable (<1s overhead per test)

---

### 4.2 Test Filesystem Snapshots

**File:** `src/app/test_runner_new/filesystem_snapshot.spl` (NEW, ~200 lines)

**Design:**

```simple
class FilesystemSnapshot:
    test_file: text
    snapshot_dir: text
    files_before: [text]
    files_after: [text]
    created: [text]
    modified: [text]
    deleted: [text]

fn snapshot_create_before(test_file: text) -> FilesystemSnapshot:
    # Record filesystem state before test
    val snapshot_dir = "/tmp/simple-test-snapshots/{random_id()}"
    dir_create(snapshot_dir)

    val files_before = dir_list_recursive("/tmp")

    FilesystemSnapshot(
        test_file: test_file,
        snapshot_dir: snapshot_dir,
        files_before: files_before,
        files_after: [],
        created: [],
        modified: [],
        deleted: []
    )

fn snapshot_capture_after(snapshot: FilesystemSnapshot) -> FilesystemSnapshot:
    # Record filesystem state after test
    val files_after = dir_list_recursive("/tmp")

    # Compute differences
    val created = files_after - snapshot.files_before  # Set difference
    val deleted = snapshot.files_before - files_after

    snapshot.files_after = files_after
    snapshot.created = created
    snapshot.deleted = deleted

    return snapshot

fn snapshot_cleanup(snapshot: FilesystemSnapshot):
    # Remove all created files
    for file in snapshot.created:
        if file.starts_with("/tmp/test_"):
            file_delete(file)

    dir_delete(snapshot.snapshot_dir)

fn snapshot_report(snapshot: FilesystemSnapshot) -> text:
    var report = "Filesystem Changes:\n"

    if snapshot.created.len() > 0:
        report = report + "  Created ({snapshot.created.len()}):\n"
        for file in snapshot.created:
            report = report + "    {file}\n"

    if snapshot.deleted.len() > 0:
        report = report + "  Deleted ({snapshot.deleted.len()}):\n"
        for file in snapshot.deleted:
            report = report + "    {file}\n"

    return report
```

**Integration:**

```simple
fn run_single_test_with_snapshot(
    test_file: text,
    config: TestConfig
) -> (TestResult, FilesystemSnapshot):
    # Create snapshot before test
    var snapshot = snapshot_create_before(test_file)

    # Run test
    val result = run_single_test(test_file, config)

    # Capture snapshot after test
    snapshot = snapshot_capture_after(snapshot)

    # Auto-cleanup temp files
    if config.auto_cleanup_temp:
        snapshot_cleanup(snapshot)

    return (result, snapshot)
```

**Testing:**

```simple
describe "filesystem_snapshot":
    it "detects created files":
        val snapshot = snapshot_create_before("test.spl")
        file_write("/tmp/test_created.txt", "data")
        snapshot = snapshot_capture_after(snapshot)

        expect(snapshot.created).to_contain("/tmp/test_created.txt")

    it "cleans up temp files":
        # Create temp file
        file_write("/tmp/test_cleanup.txt", "data")

        # Snapshot and cleanup
        var snapshot = snapshot_create_before("test.spl")
        snapshot.created = ["/tmp/test_cleanup.txt"]
        snapshot_cleanup(snapshot)

        # Verify deleted
        expect(file_exists("/tmp/test_cleanup.txt")).to_equal(false)
```

**Success Criteria:**
- [ ] Filesystem snapshot before/after test
- [ ] Detects created, modified, deleted files
- [ ] Auto-cleanup of temp files
- [ ] Snapshot reporting in test results
- [ ] 20+ test cases validating snapshot logic

---

### 4.3 Temp File Management System

**File:** `src/app/test_runner_new/temp_manager.spl` (NEW, ~250 lines)

**Design:**

```simple
class TempFileManager:
    test_file: text
    temp_dir: text
    registered_files: [text]

fn temp_manager_create(test_file: text) -> TempFileManager:
    val temp_dir = "/tmp/simple-test-{random_id()}"
    dir_create(temp_dir)

    # Set environment variable for test
    env_set("SIMPLE_TEST_TEMP_DIR", temp_dir)

    TempFileManager(
        test_file: test_file,
        temp_dir: temp_dir,
        registered_files: []
    )

fn temp_manager_register(manager: TempFileManager, file_path: text):
    # Register temp file for cleanup
    manager.registered_files = manager.registered_files + [file_path]

fn temp_manager_cleanup(manager: TempFileManager):
    # Remove all registered files
    for file in manager.registered_files:
        if file_exists(file):
            file_delete(file)

    # Remove temp directory
    dir_delete_recursive(manager.temp_dir)

    # Clear environment variable
    env_unset("SIMPLE_TEST_TEMP_DIR")

fn temp_manager_get_path(manager: TempFileManager, filename: text) -> text:
    # Get full path in temp directory
    return "{manager.temp_dir}/{filename}"
```

**Test Helper Integration:**

Add to `src/std/spec.spl`:
```simple
fn temp_file(filename: text) -> text:
    # Get temp file path (uses SIMPLE_TEST_TEMP_DIR if set)
    val temp_dir = env_get("SIMPLE_TEST_TEMP_DIR") ?? "/tmp"
    return "{temp_dir}/{filename}"

fn temp_write(filename: text, content: text):
    # Write to temp file
    val path = temp_file(filename)
    file_write(path, content)

fn temp_read(filename: text) -> text:
    # Read from temp file
    val path = temp_file(filename)
    return file_read(path)
```

**Usage in Tests:**

```simple
describe "temp file example":
    it "uses temp_file helper":
        temp_write("test.sdn", "data { value 123 }")
        val content = temp_read("test.sdn")
        expect(content).to_contain("value 123")

        # Automatically cleaned up after test
```

**Success Criteria:**
- [ ] TempFileManager creates isolated temp directories
- [ ] Environment variable passed to tests
- [ ] Auto-cleanup after test completion
- [ ] Helper functions in std.spec
- [ ] 15+ test cases validating temp management
- [ ] Migration guide for existing tests using /tmp

---

## Phase 5: Production Hardening

**Duration:** 4-5 days
**Effort:** ~16-20 hours implementation + 8-10 hours testing
**Dependencies:** Phase 1-4 complete
**Risk:** Medium

### 5.1 Distributed Test Execution

**File:** `src/app/test_runner_new/distributed_runner.spl` (NEW, ~500 lines)

**Design:**

```simple
class WorkerPool:
    size: i64
    workers: [Worker]
    task_queue: [TestTask]
    results: [TestResult]

class Worker:
    id: i64
    status: text           # "idle", "running", "stopped"
    current_task: TestTask?
    container_id: text?

class TestTask:
    test_file: text
    strategy: ExecutionStrategy
    priority: i64

fn pool_create(size: i64) -> WorkerPool:
    var workers = []
    for i in size:
        workers = workers + [Worker(
            id: i,
            status: "idle",
            current_task: nil,
            container_id: nil
        )]

    WorkerPool(
        size: size,
        workers: workers,
        task_queue: [],
        results: []
    )

fn pool_submit(pool: WorkerPool, task: TestTask):
    # Add task to queue
    pool.task_queue = pool.task_queue + [task]

fn pool_run(pool: WorkerPool) -> [TestResult]:
    # Distribute tasks to workers
    while pool.task_queue.len() > 0 or has_running_workers(pool):
        # Assign tasks to idle workers
        for worker in pool.workers:
            if worker.status == "idle" and pool.task_queue.len() > 0:
                val task = pool.task_queue[0]
                pool.task_queue = pool.task_queue[1:]  # Pop first

                worker_run_task(worker, task)

        # Check for completed workers
        for worker in pool.workers:
            if worker.status == "running":
                val completed = worker_check_completion(worker)
                if completed:
                    val result = worker_get_result(worker)
                    pool.results = pool.results + [result]
                    worker.status = "idle"

        # Small delay to avoid busy-waiting
        sleep_ms(100)

    return pool.results

fn worker_run_task(worker: Worker, task: TestTask):
    # Run test in worker (async)
    worker.current_task = task
    worker.status = "running"

    # Spawn container or process
    if task.strategy.mode == "container":
        worker.container_id = container_start_async(task.test_file, task.strategy.container_config)
    else:
        # Process-based execution
        pass_todo
```

**Task Prioritization:**

```simple
fn prioritize_tasks(tasks: [TestTask]) -> [TestTask]:
    # Sort by priority:
    # 1. Fast tests first (maximize throughput)
    # 2. Container tests batched together
    # 3. CPU-intensive tests last

    var fast = []
    var standard = []
    var slow = []

    for task in tasks:
        match task.strategy.profile.name:
            "fast": fast = fast + [task]
            "slow": slow = slow + [task]
            _: standard = standard + [task]

    return fast + standard + slow
```

**Testing:**

```simple
describe "distributed_runner":
    it "creates worker pool":
        val pool = pool_create(4)
        expect(pool.workers.len()).to_equal(4)

    it "distributes tasks to workers":
        val pool = pool_create(2)
        pool_submit(pool, TestTask(test_file: "test1.spl", ...))
        pool_submit(pool, TestTask(test_file: "test2.spl", ...))

        val results = pool_run(pool)
        expect(results.len()).to_equal(2)
```

**Success Criteria:**
- [ ] Worker pool with configurable size
- [ ] Task queue and distribution logic
- [ ] Async worker execution (process/container)
- [ ] Task prioritization
- [ ] 25+ test cases validating distributed execution
- [ ] Performance: 4x speedup with 4 workers (ideal)

---

### 5.2 CI/CD Integration

**File:** `.github/workflows/test-with-containers.yml` (NEW)

**GitHub Actions Workflow:**

```yaml
name: Test Suite (Containerized)

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

jobs:
  test-native:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Build test runner image
        run: ./scripts/docker-build-test-runner.sh

      - name: Run unit tests (native)
        run: |
          docker run --rm \
            -v $(pwd):/workspace:ro \
            --memory=512m \
            --cpus=2.0 \
            simple-test-runner:latest \
            test test/unit/ --mode=native

      - name: Run integration tests (container)
        run: |
          docker run --rm \
            -v $(pwd):/workspace:ro \
            -v /var/run/docker.sock:/var/run/docker.sock \
            --memory=2g \
            --cpus=4.0 \
            simple-test-runner:latest \
            test test/integration/ --mode=container

      - name: Generate resource report
        run: |
          docker run --rm \
            -v $(pwd):/workspace \
            simple-test-runner:latest \
            resource-report --output doc/test/resource_usage.md

      - name: Upload test results
        uses: actions/upload-artifact@v3
        with:
          name: test-results
          path: doc/test/

  test-distributed:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        worker: [1, 2, 3, 4]
    steps:
      - uses: actions/checkout@v3

      - name: Run tests (worker ${{ matrix.worker }})
        run: |
          bin/simple test \
            --distributed \
            --worker-id=${{ matrix.worker }} \
            --worker-count=4 \
            --output=results-worker-${{ matrix.worker }}.json

      - name: Upload worker results
        uses: actions/upload-artifact@v3
        with:
          name: worker-results-${{ matrix.worker }}
          path: results-worker-${{ matrix.worker }}.json

  aggregate-results:
    runs-on: ubuntu-latest
    needs: test-distributed
    steps:
      - uses: actions/download-artifact@v3
        with:
          name: worker-results-*

      - name: Aggregate results
        run: |
          bin/simple test-aggregate \
            --input results-worker-*.json \
            --output doc/test/test_result.md
```

**GitLab CI Example:**

Create `.gitlab-ci.yml`:
```yaml
stages:
  - build
  - test
  - report

build-image:
  stage: build
  script:
    - ./scripts/docker-build-test-runner.sh
    - docker tag simple-test-runner:latest $CI_REGISTRY_IMAGE:$CI_COMMIT_SHA

test-unit:
  stage: test
  image: simple-test-runner:latest
  script:
    - simple test test/unit/ --mode=native --profile=fast
  artifacts:
    reports:
      junit: test-results-unit.xml

test-integration:
  stage: test
  image: simple-test-runner:latest
  services:
    - docker:dind
  script:
    - simple test test/integration/ --mode=container --profile=slow
  artifacts:
    reports:
      junit: test-results-integration.xml

generate-report:
  stage: report
  image: simple-test-runner:latest
  script:
    - simple resource-report --output doc/test/resource_usage.md
  artifacts:
    paths:
      - doc/test/
```

**Success Criteria:**
- [ ] GitHub Actions workflow for containerized tests
- [ ] GitLab CI configuration
- [ ] Distributed test execution in CI
- [ ] Result aggregation from multiple workers
- [ ] Resource report generation and upload
- [ ] Badge integration (test pass rate, coverage)

---

### 5.3 Performance Benchmarking

**File:** `src/app/test_runner_new/benchmark.spl` (NEW, ~300 lines)

**Design:**

```simple
class BenchmarkResult:
    config_name: text
    total_tests: i64
    duration_ms: i64
    avg_test_time_ms: f64
    throughput_tests_per_sec: f64
    worker_count: i64
    execution_mode: text

fn benchmark_run_suite(config: BenchmarkConfig) -> BenchmarkResult:
    val start = time_now_ms()

    # Run full test suite
    val results = run_all_tests_with_config(config)

    val duration = time_now_ms() - start
    val avg_time = duration / results.len()
    val throughput = results.len() / (duration / 1000.0)

    BenchmarkResult(
        config_name: config.name,
        total_tests: results.len(),
        duration_ms: duration,
        avg_test_time_ms: avg_time,
        throughput_tests_per_sec: throughput,
        worker_count: config.worker_count,
        execution_mode: config.mode
    )

fn benchmark_compare_modes() -> [BenchmarkResult]:
    # Compare native, process, container modes
    var results = []

    # Native mode
    results = results + [benchmark_run_suite(BenchmarkConfig(
        name: "native",
        mode: "native",
        worker_count: 1
    ))]

    # Process mode
    results = results + [benchmark_run_suite(BenchmarkConfig(
        name: "process",
        mode: "process",
        worker_count: 1
    ))]

    # Container mode
    results = results + [benchmark_run_suite(BenchmarkConfig(
        name: "container",
        mode: "container",
        worker_count: 1
    ))]

    return results

fn benchmark_scale_workers() -> [BenchmarkResult]:
    # Test worker scaling (1, 2, 4, 8 workers)
    var results = []

    for workers in [1, 2, 4, 8]:
        results = results + [benchmark_run_suite(BenchmarkConfig(
            name: "workers-{workers}",
            mode: "process",
            worker_count: workers
        ))]

    return results

fn benchmark_generate_report(results: [BenchmarkResult]) -> text:
    var report = "# Test Runner Performance Benchmark\n\n"

    report = report + "| Configuration | Tests | Duration | Avg Time | Throughput |\n"
    report = report + "|--------------|-------|----------|----------|------------|\n"

    for result in results:
        report = report + "| {result.config_name} | {result.total_tests} | "
        report = report + "{result.duration_ms}ms | {result.avg_test_time_ms}ms | "
        report = report + "{result.throughput_tests_per_sec} tests/sec |\n"

    return report
```

**Benchmark Scenarios:**

1. **Execution Mode Comparison**: Native vs Process vs Container
2. **Worker Scaling**: 1, 2, 4, 8 workers
3. **Profile Impact**: Fast vs Standard vs Slow profiles
4. **Isolation Overhead**: Native vs Strict vs Paranoid isolation
5. **Container Engine**: Docker vs Podman

**CLI Integration:**

```bash
# Run all benchmarks
bin/simple test-benchmark --all

# Compare modes
bin/simple test-benchmark --compare-modes

# Scale workers
bin/simple test-benchmark --scale-workers

# Generate report
bin/simple test-benchmark --report doc/test/benchmark_report.md
```

**Success Criteria:**
- [ ] Benchmark harness implemented
- [ ] 5+ benchmark scenarios
- [ ] Markdown report generation
- [ ] Performance baseline established
- [ ] Scaling efficiency measured (linear, sub-linear)
- [ ] Overhead quantified (<10% for container mode)

---

### 5.4 Monitoring Dashboard

**File:** `src/app/test_runner_new/dashboard.spl` (NEW, ~400 lines)

**Design:**

Web-based dashboard for real-time test monitoring (Simple HTTP server).

**Features:**
- Real-time test progress
- Resource usage graphs (CPU, memory)
- Violation alerts
- Worker status
- Test queue visualization

**Implementation:**

```simple
fn dashboard_start(port: i64):
    # Start HTTP server on port
    val server = http_server_create(port)

    # Register routes
    server_route(server, "/", dashboard_index)
    server_route(server, "/api/status", dashboard_api_status)
    server_route(server, "/api/workers", dashboard_api_workers)
    server_route(server, "/api/results", dashboard_api_results)

    # Start server
    http_server_start(server)

fn dashboard_index(request: HttpRequest) -> HttpResponse:
    # Serve HTML dashboard
    val html = file_read("src/app/test_runner_new/dashboard.html")
    HttpResponse(
        status: 200,
        headers: [("Content-Type", "text/html")],
        body: html
    )

fn dashboard_api_status(request: HttpRequest) -> HttpResponse:
    # Return JSON status
    val status = {
        "total_tests": 4067,
        "completed": global_runner_state.completed_count,
        "running": global_runner_state.running_count,
        "failed": global_runner_state.failed_count,
        "duration_ms": time_now_ms() - global_runner_state.start_time
    }

    HttpResponse(
        status: 200,
        headers: [("Content-Type", "application/json")],
        body: json_encode(status)
    )
```

**HTML Dashboard** (`src/app/test_runner_new/dashboard.html`):

```html
<!DOCTYPE html>
<html>
<head>
    <title>Simple Test Runner Dashboard</title>
    <style>
        body { font-family: monospace; padding: 20px; }
        .status { display: flex; gap: 20px; }
        .metric { border: 1px solid #ccc; padding: 10px; }
        .progress { width: 100%; height: 20px; background: #eee; }
        .progress-bar { height: 100%; background: #4caf50; }
    </style>
</head>
<body>
    <h1>Simple Test Runner Dashboard</h1>

    <div class="status">
        <div class="metric">
            <div>Total Tests</div>
            <div id="total-tests">0</div>
        </div>
        <div class="metric">
            <div>Completed</div>
            <div id="completed">0</div>
        </div>
        <div class="metric">
            <div>Running</div>
            <div id="running">0</div>
        </div>
        <div class="metric">
            <div>Failed</div>
            <div id="failed">0</div>
        </div>
    </div>

    <h2>Progress</h2>
    <div class="progress">
        <div class="progress-bar" id="progress-bar"></div>
    </div>

    <h2>Workers</h2>
    <table id="workers"></table>

    <script>
        // Poll API every 1 second
        setInterval(updateDashboard, 1000);

        function updateDashboard() {
            fetch('/api/status')
                .then(r => r.json())
                .then(data => {
                    document.getElementById('total-tests').textContent = data.total_tests;
                    document.getElementById('completed').textContent = data.completed;
                    document.getElementById('running').textContent = data.running;
                    document.getElementById('failed').textContent = data.failed;

                    const progress = (data.completed / data.total_tests) * 100;
                    document.getElementById('progress-bar').style.width = progress + '%';
                });
        }
    </script>
</body>
</html>
```

**CLI Integration:**

```bash
# Start test runner with dashboard
bin/simple test --dashboard --dashboard-port=8080

# Open browser to http://localhost:8080
```

**Success Criteria:**
- [ ] HTTP server implementation
- [ ] HTML dashboard with real-time updates
- [ ] API endpoints for status, workers, results
- [ ] Auto-refresh every 1 second
- [ ] Resource graphs (optional, using Chart.js)

---

## Implementation Timeline

### Week 1: Foundation
- **Day 1-2:** Phase 1.1 - process_run_with_limits()
- **Day 3:** Phase 1.2 - Resource profiles
- **Day 4:** Phase 1.3 - Test runner integration
- **Day 5:** Testing and validation

### Week 2: Containers
- **Day 1:** Phase 2.1 - Docker image
- **Day 2-3:** Phase 2.2 - Container backend
- **Day 4:** Phase 2.3 - Hybrid execution
- **Day 5:** Testing and validation

### Week 3: Monitoring
- **Day 1-2:** Phase 3.1 - Resource monitoring
- **Day 3:** Phase 3.2 - Violation detection
- **Day 4:** Phase 3.3 - Resource database
- **Day 5:** Testing and validation

### Week 4: Advanced Isolation
- **Day 1-2:** Phase 4.1 - Per-test containers
- **Day 3:** Phase 4.2 - Filesystem snapshots
- **Day 4:** Phase 4.3 - Temp file management
- **Day 5:** Testing and validation

### Week 5: Production
- **Day 1-2:** Phase 5.1 - Distributed execution
- **Day 3:** Phase 5.2 - CI/CD integration
- **Day 4:** Phase 5.3 - Benchmarking
- **Day 5:** Phase 5.4 - Dashboard

**Total:** ~5 weeks (25 days)

---

## Resource Estimates

### Development Effort
- **Phase 1:** 12 hours
- **Phase 2:** 20 hours
- **Phase 3:** 16 hours
- **Phase 4:** 24 hours
- **Phase 5:** 20 hours
- **Total:** ~92 hours (~2.5 weeks full-time)

### Testing Effort
- **Phase 1:** 6 hours
- **Phase 2:** 10 hours
- **Phase 3:** 8 hours
- **Phase 4:** 12 hours
- **Phase 5:** 10 hours
- **Total:** ~46 hours (~1 week full-time)

### Infrastructure
- **Docker Hub storage:** ~100MB for images
- **CI/CD minutes:** ~500 min/month (GitHub Actions free tier)
- **Database storage:** ~50MB for resource tracking

---

## Success Metrics

### Phase 1 (Foundation)
- [ ] process_run_with_limits() enforces CPU/memory limits (±10% accuracy)
- [ ] 4 resource profiles defined and configurable
- [ ] Test runner applies profiles automatically
- [ ] 0 regressions in existing 4,067 tests

### Phase 2 (Containers)
- [ ] Docker image builds in <5 min
- [ ] Container execution overhead <10%
- [ ] Hybrid execution strategy working (native/process/container)
- [ ] Full test suite runs in containers

### Phase 3 (Monitoring)
- [ ] Resource monitoring with <5% overhead
- [ ] Violation detection accuracy >95%
- [ ] Resource database tracking 7+ days history
- [ ] Automated reports generated

### Phase 4 (Advanced Isolation)
- [ ] Per-test container isolation <1s overhead
- [ ] Filesystem snapshots detect temp file leaks
- [ ] Auto-cleanup reduces /tmp usage by 90%
- [ ] Security profiles enforced (seccomp, apparmor)

### Phase 5 (Production)
- [ ] Distributed execution with 4 workers = 3.5x speedup
- [ ] CI/CD integration on GitHub Actions + GitLab
- [ ] Benchmark report shows <15% container overhead
- [ ] Dashboard provides real-time monitoring

---

## Risk Mitigation

### High-Risk Items
1. **Container performance overhead**: Benchmark early, optimize if >15%
2. **Distributed execution complexity**: Start with simple worker pool, iterate
3. **Resource monitoring accuracy**: Validate against known workloads

### Fallback Plans
- **If containers too slow**: Use process isolation with ulimit
- **If distributed execution buggy**: Keep single-threaded mode as default
- **If monitoring overhead high**: Make monitoring opt-in

---

## Future Enhancements

### Beyond Phase 5
- **Kubernetes integration**: Run tests in K8s pods
- **Remote workers**: Distribute tests across multiple machines
- **GPU resource management**: Track GPU usage for ML tests
- **Test result caching**: Skip unchanged tests (like Bazel)
- **Fuzzing integration**: Continuous fuzzing in test suite
- **Coverage-guided testing**: Prioritize tests by code coverage

---

## Conclusion

This plan transforms the Simple Language test runner from a fast, functional system into a production-grade testing platform with:

1. **Robust isolation**: Process and container-based isolation preventing interference
2. **Resource enforcement**: CPU, memory, timeout limits strictly enforced
3. **Scalability**: Distributed execution with worker pools
4. **Observability**: Real-time monitoring, violation detection, historical tracking
5. **Production-ready**: CI/CD integration, security hardening, performance optimization

**Estimated Effort:** 92 hours development + 46 hours testing = **138 hours total** (~3.5 weeks full-time)

**Risk Level:** Medium (mainly container performance and distributed execution complexity)

**Expected Outcome:** Zero test flakiness, predictable resource usage, 3-4x faster execution with parallelization, production-grade reliability.
