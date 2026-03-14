# Test Runner Complete Status Report & Implementation Plan

**Date:** 2026-02-14
**Research Method:** Multi-agent analysis (4 specialized agents)

## Executive Summary

**Current Completion: 75%** - Core infrastructure solid, missing parallel execution and advanced features

**What Works:**
- ✅ CLI interface with 40+ flags
- ✅ Sequential test execution (interpreter/SMF/native)
- ✅ Container isolation (sequential mode)
- ✅ Resource limit enforcement (ulimit-based)
- ✅ System monitoring (CPU/memory)
- ✅ Process tracking and cleanup
- ✅ Checkpoint/resume functionality
- ✅ Test discovery and filtering

**What's Missing:**
- ❌ True parallel test execution (async spawn not wired)
- ❌ Container tracking for long-running tests
- ❌ Per-test resource overrides
- ❌ Signal handlers (Ctrl+C cleanup)
- ❌ I/O limit enforcement
- ❌ Test metadata system
- ❌ Dynamic resource adjustment

---

## Part 1: Current Implementation Status

### 1.1 CLI Features (40+ flags implemented)

**Test Selection:**
```bash
--unit                    # Only unit tests
--integration             # Only integration tests
--system                  # Only system tests
--tag NAME               # Filter by tag
--only-slow              # slow_it tests only
--only-skipped           # Skipped tests only
--planned-only           # Pending tests
```

**Execution Modes:**
```bash
--mode interpreter       # Tree-walk interpreter (default)
--mode smf               # SMF bytecode loader
--mode native            # Native x86_64 compilation
--execution-mode container-seq   # Sequential containers
```

**Resource Control:**
```bash
--timeout N              # Global timeout (default: 120s)
--cpu-threshold PERCENT  # Self-protection CPU limit (80%)
--mem-threshold PERCENT  # Self-protection memory limit (80%)
--self-protect           # Enable monitoring every 5 tests
--safe-mode              # Enable resource limits
--no-limits              # Disable all limits
```

**Container Control:**
```bash
--container-sequential   # Max isolation per test
--resume                 # Resume from checkpoint
```

**Output & Debugging:**
```bash
--verbose / -v           # Verbose output
--list                   # List tests without running
--show-tags              # Display tags
--coverage               # Code coverage
--fail-fast              # Stop on first failure
--keep-artifacts         # Keep build artifacts
```

### 1.2 Execution Strategies (5 modes)

| Strategy | Isolation | Resource Enforcement | Use Case |
|----------|-----------|---------------------|----------|
| **Native** | None | None | Fast unit tests (256MB, 60s) |
| **Process** | ulimit | CPU/Memory/FDs | Standard tests (512MB, 300s) |
| **Safe** | ulimit + timeout | All limits | Integration tests (512MB, 300s) |
| **Container** | Docker/Podman | Memory + CPU | Heavy tests (2GB, 1800s) |
| **ContainerSeq** | Per-test container | Full isolation | Max isolation (512MB, 600s) |

**Auto-Selection by Path:**
```
test/unit/         → Native (fast)
test/integration/  → Safe (standard)
test/system/       → Safe (slow)
test/qemu/         → Container (intensive)
test/baremetal/    → Container (intensive)
test/database/     → Process (slow)
```

### 1.3 Resource Limit Profiles

| Profile | CPU Time | Memory | Timeout | FDs | Procs | Use Case |
|---------|----------|--------|---------|-----|-------|----------|
| **fast** | 1s | 128MB | 2s | 100 | 10 | Unit tests |
| **standard** | 5s | 512MB | 10s | 500 | 50 | Regular tests |
| **slow** | 30s | 1GB | 60s | 1000 | 100 | Integration |
| **intensive** | 120s | 4GB | 300s | 2000 | 200 | QEMU, compiler |
| **critical** | 600s | 8GB | 900s | 4000 | 500 | Infrastructure |

### 1.4 Container Implementation

**Container Modes:**
1. **Sequential Container** (`sequential_container.spl`)
   - One isolated container per test file
   - 512 MB memory, 1.0 CPU cores
   - Network: none (isolated)
   - Auto-cleanup with `--rm` flag

2. **Docker Compose** (`docker-compose.yml`)
   - Four service profiles: unit/integration/system/all
   - Parallel tiers (not wired to runner)
   - Dev shell for debugging

3. **Base Image** (`docker/Dockerfile.test-isolation`)
   - Alpine 3.18 (~40 MB total)
   - Non-root user (testuser, UID 1001)
   - Security: all capabilities dropped, read-only FS
   - Health check: `simple --version`

**Container Resource Enforcement:**
```bash
docker run --rm \
  --memory=512m \
  --cpus=1.0 \
  --network=none \
  -v $(pwd):/workspace:rw \
  simple-test-isolation:latest test test/unit/spec.spl
```

### 1.5 Process Limit Enforcement

**Unix/Linux** (`process_run_with_limits()`):
```bash
ulimit -v {memory_kb};      # Virtual memory
ulimit -t {cpu_seconds};    # CPU time
ulimit -n {max_fds};        # File descriptors
exec timeout --kill-after=5s {timeout}s {cmd}
```

**Violation Detection:**
- Exit code 124 → timeout
- Exit code 137 → SIGKILL (hard timeout)
- Exit code 139 → SIGSEGV (memory violation)
- Stderr patterns: "cpu time limit exceeded", "cannot allocate memory", etc.

**Windows:** Timeout-only mode (no ulimit support)

### 1.6 System Monitoring

**SystemResources Tracking:**
```simple
struct SystemResources:
    cpu_percent: f64          # 0-100 (all cores)
    memory_percent: f64       # 0-100 (used/total)
    memory_used_mb: i64
    memory_total_mb: i64
```

**Platform-Specific:**
- **Linux:** `/proc/stat` (CPU), `/proc/meminfo` (memory)
- **macOS:** `top -l 1` (CPU), `vm_stat` (memory)
- **Windows:** `wmic` commands (stub implementation)

**Self-Protection:**
```simple
# In main test loop (every 5 tests)
val (exceeded, reason) = system_exceeds_threshold(80, 90)
if exceeded:
    shutdown_graceful(reason, completed, passed, failed, skipped)
```

### 1.7 Process Tracking & Cleanup

**Lifecycle Management** (`process_tracker.spl`, `runner_lifecycle.spl`):
```simple
# Spawn with automatic tracking
val pid = spawn_tracked_process("simple", ["test.spl"])

# Automatic cleanup on exit
cleanup_all_children()  # Kills all tracked processes + containers
```

**Graceful Shutdown Sequence:**
1. Save checkpoint → `.simple-test-checkpoint.sdn`
2. Kill child processes → SIGTERM (2s) → SIGKILL
3. Stop containers → `docker stop -t 10` → `docker rm -f`
4. Exit with code 42 (EXIT_RESOURCE_SHUTDOWN)

**Resume Capability:**
```bash
# After shutdown
bin/simple test --resume
# Skips completed tests, continues from checkpoint
```

### 1.8 Test Discovery & Filtering

**Discovery Mechanism:**
- Pattern: `*_spec.spl` or `*_test.spl`
- Recursive directory walk
- Level filtering: `--unit`, `--integration`, `--system`
- Content filtering: `--only-slow`, `--only-skipped`, `--tag`

**Filters Available:**
```simple
# Path-based
discover_test_files("test/unit/", options)  # Only unit tests

# Content-based
--only-slow      # Searches for "slow_it " in file
--only-skipped   # Searches for 'tag: "skip"'
--tag=database   # Searches for 'tag: "database"'
```

---

## Part 2: Critical Gaps

### 2.1 TRUE PARALLEL EXECUTION ❌

**Current State:**
- `test_runner_parallel.spl` exists but runs **sequential batches**
- Code comment: `"rt_process_spawn_async not yet available for parallel execution"`
- Batch size = CPU cores - 1, but processes sequentially

**What's Missing:**
```simple
# Need async spawn API:
val pids = []
for test in batch:
    val pid = process_spawn_async("simple", [test])
    pids.push(pid)

# Wait for all
for pid in pids:
    val code = process_wait(pid, timeout_ms)
```

**Blockers:**
- `rt_process_spawn_async()` exists in `process_ops.spl`
- Not wired into test runner main loop
- No stdout/stderr capture for async processes

### 2.2 CONTAINER TRACKING FOR LONG-RUNNING TESTS ❌

**Current State:**
- Containers use `--rm` flag (auto-remove on exit)
- No tracking of container IDs
- Can't stop runaway containers

**What's Missing:**
```simple
# Need named containers without --rm
val container_id = run_tracked_container(...)
tracker_register_container(container_id)

# On timeout or Ctrl+C
tracker_stop_all_containers()  # Calls docker stop + rm
```

**Issue:**
- Long-running tests (QEMU, baremetal) may hang
- No way to kill container if test runner crashes
- Heartbeat monitoring exists but not integrated

### 2.3 PER-TEST RESOURCE OVERRIDES ❌

**Current State:**
- Resource profiles only at category level (unit/integration/system)
- Individual tests can't override timeout or memory limit
- `--timeout` flag is global

**What's Missing:**
```simple
# Test metadata in file header
# @Timeout 600
# @Memory 2048
# @CPU 2.0
# @Profile intensive

describe "heavy integration test":
    # Uses overridden limits instead of category defaults
```

**Needed:**
- Parse test file headers for metadata
- Override profile per-test
- TestMetadata struct with timeout_override, memory_override, etc.

### 2.4 SIGNAL HANDLERS (Ctrl+C CLEANUP) ❌

**Current State:**
- `shutdown.spl` defines cleanup sequence
- Not triggered by SIGTERM/SIGINT
- Manual interrupt leaves orphaned processes

**What's Missing:**
```simple
# Need SFFI additions
extern fn rt_signal_handler_install(signal: i64, handler: fn())
extern fn rt_atexit_register(handler: fn())

# Install on startup
fn main():
    install_signal_handlers()
    run_tests()

fn on_sigint():
    cleanup_and_exit(130, "SIGINT (Ctrl+C)")
```

**Blocker:** Requires SFFI additions to `src/compiler_seed/runtime.c`

### 2.5 I/O LIMIT ENFORCEMENT ❌

**Current State:**
- I/O limits defined in profiles (ops/sec)
- NOT enforced in Docker commands
- No `--device-read-iops` or `--device-write-iops`

**What's Missing:**
```bash
# Need Docker I/O limits
docker run \
  --device-read-bps /dev/sda:10mb \
  --device-write-bps /dev/sda:10mb \
  --device-read-iops /dev/sda:1000 \
  --device-write-iops /dev/sda:1000
```

**Impact:** I/O-heavy tests can contend for disk resources

### 2.6 TEST METADATA SYSTEM ❌

**Current State:**
- Metadata only in comments: `# @Feature 708.1`, `# @Description ...`
- Not parsed or used by runner
- Tags are string-matched in file content

**What's Missing:**
```simple
struct TestMetadata:
    priority: text           # "P0", "P1", "P2"
    tags: [text]             # ["smoke", "regression", "security"]
    timeout_override: i64    # Per-test timeout
    memory_override: i64     # Per-test memory
    cpu_override: f64        # Per-test CPU cores
    isolation_level: text    # "none", "process", "container"
    dependencies: [text]     # Test files that must pass first
```

**Needed:**
- Parse headers: `# @Priority P0`, `# @Tag smoke`
- Store in TestFileResult
- Filter by: `--priority=P0`, `--tag=smoke`

### 2.7 DYNAMIC RESOURCE ADJUSTMENT ❌

**Current State:**
- `system_exceeds_threshold()` monitors but doesn't adjust
- Static thresholds (80% CPU, 90% memory)
- No adaptive limit reduction

**What's Missing:**
```simple
# Adaptive adjustment
if system_cpu > 80%:
    # Reduce test process CPU limit
    new_limit = current_limit * 0.5
    adjust_resource_limits(new_limit)
```

**Use Case:** High system load → reduce test resource allocation

### 2.8 CONTAINER RESOURCE METRICS CAPTURE ❌

**Current State:**
- No `docker stats` integration
- Can't correlate container resource usage with test results

**What's Missing:**
```bash
# Capture peak metrics
docker stats --no-stream {container_id}
# Parse: CPU %, MEM USAGE / LIMIT, NET I/O, BLOCK I/O

# Store in TestFileResult
result.max_cpu_percent = 45.2
result.max_memory_mb = 128
```

### 2.9 CONTINUOUS PROCESS MONITORING ❌

**Current State:**
- `sample_process(pid)` takes single snapshot
- No peak value tracking during execution

**What's Missing:**
```simple
fn monitor_until_exit(pid, interval_ms) -> ProcessMetrics:
    # Background thread sampling
    var peak_cpu = 0.0
    var peak_memory = 0

    while process_is_running(pid):
        val metrics = sample_process(pid)
        peak_cpu = max(peak_cpu, metrics.cpu_percent)
        peak_memory = max(peak_memory, metrics.memory_mb)
        sleep(interval_ms)

    ProcessMetrics(peak_cpu, peak_memory, ...)
```

**Blocker:** Requires threading or async I/O

### 2.10 TEST DEPENDENCIES & ORDERING ❌

**Current State:**
- Tests run in discovery order
- No dependency tracking
- `pending_on()` mentioned but not implemented

**What's Missing:**
```simple
# In test file
# @DependsOn test/unit/database_spec.spl

describe "integration test":
    # Only runs if database_spec passes
```

**Needed:**
- Dependency graph resolution
- Topological sort for test ordering
- Skip dependent tests if prerequisite fails

---

## Part 3: Implementation Plan

### Phase 1: Parallel Execution (HIGH PRIORITY)

**Goal:** Enable true parallel test execution with process limits

**Tasks:**
1. Wire `process_spawn_async()` into test runner main loop
2. Implement stdout/stderr capture for async processes
   - Option A: Redirect to temp files
   - Option B: Use pipes (requires SFFI)
3. Create async result collector
4. Add `--parallel` flag (default: sequential)
5. Add `--max-workers N` flag (default: CPU cores - 1)

**Implementation:**
```simple
fn run_tests_parallel(files: [text], options: TestOptions) -> TestRunResult:
    val max_workers = options.max_workers ?? (cpu_count() - 1)
    var pids: [i64] = []
    var pid_to_file: Dict = {}
    var results: [TestFileResult] = []

    for file in files:
        # Wait if at max capacity
        while pids.len() >= max_workers:
            val completed_pid = wait_for_any(pids, timeout_ms)
            collect_result(completed_pid, pid_to_file, results)
            pids.remove(completed_pid)

        # Spawn new test
        val pid = spawn_tracked_process("simple", [file])
        pids.push(pid)
        pid_to_file[pid] = file

    # Wait for remaining
    for pid in pids:
        collect_result(pid, pid_to_file, results)

    aggregate_results(results)
```

**Files to Modify:**
- `src/app/test_runner_new/test_runner_main.spl`
- `src/app/test_runner_new/test_runner_parallel.spl`
- `src/app/test_runner_new/test_runner_args.spl` (add --parallel flag)

**Estimated Effort:** 2-3 hours

---

### Phase 2: Container Tracking & Cleanup (HIGH PRIORITY)

**Goal:** Enable container tracking for long-running tests

**Tasks:**
1. Remove `--rm` flag from container runs
2. Generate unique container names
3. Track container IDs in `process_tracker.spl`
4. Implement `tracker_stop_all_containers()` integration
5. Add container cleanup on shutdown

**Implementation:**
```simple
fn run_tracked_container(...) -> text:
    val container_name = "simple-test-{timestamp}-{random}"

    val cmd = "{runtime} run -d \
        --name {container_name} \
        --memory={memory_mb}m \
        --cpus={cpu_count} \
        {image} test {test_file}"

    val container_id = shell_output(cmd, "")
    tracker_register_container(container_id)

    container_id
```

**Files to Modify:**
- `src/app/test_runner_new/test_runner_container.spl`
- `src/app/test_runner_new/sequential_container.spl`
- `src/app/test_runner_new/process_tracker.spl` (already has tracker_stop_all_containers)

**Estimated Effort:** 1-2 hours

---

### Phase 3: Per-Test Metadata System (MEDIUM PRIORITY)

**Goal:** Enable per-test resource overrides and filtering

**Tasks:**
1. Create `TestMetadata` struct
2. Implement header parser
3. Add metadata to `TestFileResult`
4. Support `--priority`, `--tag` filtering with parsed metadata
5. Override resource profiles per-test

**Implementation:**
```simple
struct TestMetadata:
    priority: text           # P0/P1/P2
    tags: [text]
    timeout_override: i64
    memory_override: i64
    cpu_override: f64
    isolation_override: text
    dependencies: [text]

fn parse_test_metadata(file_path: text) -> TestMetadata:
    val content = file_read(file_path)
    val lines = content.split(NL)

    var priority = ""
    var tags: [text] = []
    var timeout = 0

    for line in lines:
        if line.starts_with("# @Priority "):
            priority = line[12:].trim()
        elif line.starts_with("# @Tag "):
            tags.push(line[7:].trim())
        elif line.starts_with("# @Timeout "):
            timeout = to_int(line[11:].trim())

    TestMetadata(priority, tags, timeout, ...)
```

**Files to Create:**
- `src/app/test_runner_new/test_metadata.spl`

**Files to Modify:**
- `src/app/test_runner_new/test_runner_files.spl` (add metadata parsing)
- `src/app/test_runner_new/test_runner_types.spl` (add TestMetadata struct)

**Estimated Effort:** 2-3 hours

---

### Phase 4: Signal Handlers (BLOCKED - requires SFFI)

**Goal:** Enable Ctrl+C cleanup

**SFFI Additions Needed:**
```c
// In src/compiler_seed/runtime.c
void rt_signal_handler_install(int64_t signal, void (*handler)(void));
void rt_atexit_register(void (*handler)(void));
```

**Implementation (once SFFI available):**
```simple
extern fn rt_signal_handler_install(signal: i64, handler: fn())
extern fn rt_atexit_register(handler: fn())

fn install_signal_handlers():
    rt_signal_handler_install(2, on_sigint)    # SIGINT
    rt_signal_handler_install(15, on_sigterm)  # SIGTERM
    rt_atexit_register(on_normal_exit)

fn on_sigint():
    cleanup_and_exit(130, "SIGINT (Ctrl+C)")

fn on_sigterm():
    cleanup_and_exit(143, "SIGTERM")

fn on_normal_exit():
    cleanup_all_children()
```

**Files to Modify:**
- `src/compiler_seed/runtime.c` (SFFI additions)
- `src/app/test_runner_new/runner_lifecycle.spl`
- `src/app/cli/main.spl` (call install_signal_handlers on startup)

**Estimated Effort:** 3-4 hours (including SFFI)

---

### Phase 5: I/O Limit Enforcement (LOW PRIORITY)

**Goal:** Enforce I/O limits in containers

**Implementation:**
```simple
fn build_container_io_limits(profile: ResourceProfile) -> text:
    var flags = ""
    if profile.max_io_ops > 0:
        flags = flags + "--device-read-iops /dev/sda:{profile.max_io_ops} "
        flags = flags + "--device-write-iops /dev/sda:{profile.max_io_ops} "
    flags
```

**Files to Modify:**
- `src/app/test_runner_new/test_runner_container.spl`
- `src/app/test_runner_new/sequential_container.spl`

**Estimated Effort:** 1 hour

---

### Phase 6: Continuous Monitoring (MEDIUM PRIORITY)

**Goal:** Capture peak resource usage during test execution

**Implementation:**
```simple
fn monitor_test_execution(pid: i64) -> ProcessMetrics:
    var samples: [ProcessMetrics] = []

    while process_is_running(pid):
        val metrics = sample_process(pid)
        samples.push(metrics)
        sleep(100)  # 100ms sampling interval

    # Return peak values
    ProcessMetrics(
        pid: pid,
        cpu_percent: max(samples.map(\s: s.cpu_percent)),
        memory_mb: max(samples.map(\s: s.memory_mb)),
        ...
    )
```

**Files to Modify:**
- `src/lib/process_monitor.spl`
- `src/app/test_runner_new/test_runner_resources.spl`

**Estimated Effort:** 2 hours

---

## Part 4: Command-Line Interface Enhancements

### 4.1 New Flags Needed

```bash
# Parallel execution
--parallel               # Enable parallel test execution
--max-workers N          # Max parallel workers (default: CPU cores - 1)
--parallel-timeout N     # Timeout for parallel batch (default: 300s)

# Container control
--container-track        # Track container IDs (don't use --rm)
--container-cleanup      # Force cleanup all simple-test-* containers

# Resource overrides (per-test metadata)
--priority P0|P1|P2     # Filter by priority
--tag NAME              # Filter by tag (already exists, enhance)
--isolation none|process|container  # Override isolation level

# Advanced filtering
--depends-on FILE       # Run tests depending on FILE
--no-dependencies       # Skip dependency resolution

# Monitoring
--monitor-interval MS   # Resource sampling interval (default: 100ms)
--capture-metrics       # Capture peak CPU/memory per test
--resource-report       # Generate resource usage report

# Signal handling (once SFFI available)
--no-signal-handlers    # Disable Ctrl+C handling (for debugging)
```

### 4.2 Configuration File Enhancements

**simple.test.sdn additions:**
```sdn
test_config {
  # Parallel execution
  parallel true
  max_workers 4

  # Container tracking
  container_track true
  container_cleanup_on_exit true

  # Resource monitoring
  monitor_interval_ms 100
  capture_metrics true

  # Metadata
  metadata_parse true
  metadata_cache_path "doc/test/metadata_cache.sdn"

  # Dependencies
  resolve_dependencies true
  skip_failed_dependencies true
}
```

---

## Part 5: Prioritized Implementation Roadmap

### Week 1: Core Robustness (IMMEDIATE)

**Focus:** Make test runner production-ready for long-running tests

1. ✅ Process tracking & cleanup (DONE - implemented 2026-02-14)
2. ✅ Graceful shutdown with checkpoint (DONE - implemented 2026-02-14)
3. ✅ Resume from checkpoint (DONE - implemented 2026-02-14)
4. ⏳ Container tracking (PENDING - Phase 2, ~2 hours)
5. ⏳ Parallel execution (PENDING - Phase 1, ~3 hours)

**Deliverable:** Test runner can run 1000+ tests in parallel with resource limits and automatic cleanup

---

### Week 2: Advanced Features (HIGH VALUE)

**Focus:** Per-test control and metadata

1. ⏳ Test metadata parser (PENDING - Phase 3, ~3 hours)
2. ⏳ Per-test resource overrides (PENDING - Phase 3, ~2 hours)
3. ⏳ Priority/tag filtering (PENDING - Phase 3, ~1 hour)
4. ⏳ Continuous monitoring (PENDING - Phase 6, ~2 hours)

**Deliverable:** Fine-grained control over individual test resource allocation

---

### Week 3: Signal Handling & I/O (BLOCKED)

**Focus:** Complete resource control

1. ⏳ Signal handlers (BLOCKED - requires SFFI, ~4 hours)
2. ⏳ I/O limit enforcement (PENDING - Phase 5, ~1 hour)
3. ⏳ Test dependencies (PENDING - future phase, ~4 hours)

**Deliverable:** Full resource isolation and dependency management

---

## Part 6: File Modification Summary

### Files to Create (Phase 1-3):
1. `src/app/test_runner_new/test_metadata.spl` (~150 lines)
2. `doc/report/parallel_execution_design_2026-02-14.md` (design doc)

### Files to Modify (Phase 1-3):
1. `src/app/test_runner_new/test_runner_main.spl` (add parallel loop)
2. `src/app/test_runner_new/test_runner_parallel.spl` (implement true async)
3. `src/app/test_runner_new/test_runner_args.spl` (add --parallel flags)
4. `src/app/test_runner_new/test_runner_container.spl` (remove --rm, add tracking)
5. `src/app/test_runner_new/sequential_container.spl` (container ID tracking)
6. `src/app/test_runner_new/test_runner_files.spl` (add metadata parsing)
7. `src/app/test_runner_new/test_runner_types.spl` (add TestMetadata struct)
8. `src/lib/process_monitor.spl` (continuous monitoring)

### Files to Modify (Phase 4 - SFFI):
1. `src/compiler_seed/runtime.c` (signal handler SFFI)
2. `src/app/test_runner_new/runner_lifecycle.spl` (signal setup)
3. `src/app/cli/main.spl` (install handlers on startup)

---

## Part 7: Testing Strategy

### Integration Tests Needed:
1. `test/integration/parallel_execution_spec.spl` (parallel mode)
2. `test/integration/container_tracking_spec.spl` (container cleanup)
3. `test/integration/metadata_override_spec.spl` (per-test limits)
4. `test/integration/signal_handling_spec.spl` (Ctrl+C cleanup)

### Manual Test Scenarios:
```bash
# Test 1: Parallel execution with limits
bin/simple test --parallel --max-workers=4 --self-protect test/unit/

# Test 2: Container tracking
bin/simple test --execution-mode=container-seq --container-track test/integration/

# Test 3: Per-test overrides
# Create test with: # @Timeout 600, # @Memory 2048
bin/simple test test/integration/heavy_spec.spl

# Test 4: Ctrl+C cleanup (once SFFI available)
bin/simple test test/ &
kill -INT $!
docker ps  # Should show no orphaned containers

# Test 5: Long-running with checkpoint
bin/simple test --self-protect --cpu-limit=50 test/
# Should trigger shutdown after ~150 tests
bin/simple test --resume
# Should continue from checkpoint
```

---

## Summary Table: Completion Status

| Feature | Status | Priority | Effort | Blocker |
|---------|--------|----------|--------|---------|
| **CLI flags (40+)** | ✅ DONE | - | - | - |
| **Sequential execution** | ✅ DONE | - | - | - |
| **Container sequential** | ✅ DONE | - | - | - |
| **Resource profiles** | ✅ DONE | - | - | - |
| **ulimit enforcement** | ✅ DONE | - | - | - |
| **System monitoring** | ✅ DONE | - | - | - |
| **Process tracking** | ✅ DONE | - | - | - |
| **Graceful shutdown** | ✅ DONE | - | - | - |
| **Checkpoint/resume** | ✅ DONE | - | - | - |
| **Test discovery** | ✅ DONE | - | - | - |
| **Parallel execution** | ❌ MISSING | HIGH | 3h | Async wiring |
| **Container tracking** | ❌ MISSING | HIGH | 2h | None |
| **Per-test metadata** | ❌ MISSING | MEDIUM | 3h | None |
| **Per-test overrides** | ❌ MISSING | MEDIUM | 2h | Metadata parser |
| **Signal handlers** | ❌ MISSING | HIGH | 4h | SFFI additions |
| **I/O limits** | ❌ MISSING | LOW | 1h | None |
| **Continuous monitoring** | ❌ MISSING | MEDIUM | 2h | None |
| **Test dependencies** | ❌ MISSING | LOW | 4h | Metadata system |

**Total Estimated Effort (Phases 1-3):** ~15 hours
**Total Estimated Effort (All Phases):** ~23 hours

---

## Conclusion

The Simple test runner is **75% complete** with solid core infrastructure. The remaining 25% consists of:
- Parallel execution (most impactful)
- Container tracking (robustness)
- Metadata system (flexibility)
- Signal handling (requires SFFI)

**Recommendation:** Implement Phases 1-3 immediately (15 hours total) for production readiness. Defer Phase 4 until SFFI signal handling is available.
