# Robust Test Runner with Container and Process Isolation - Research and Best Practices

**Date:** 2026-02-14
**Status:** Research Complete - Implementation Ready
**Type:** Research Document (Best Practices Guide)

---

## Executive Summary

This document outlines best practices and implementation strategies for robust test isolation using containers and process isolation. Based on industry research and analysis of the Simple Language test infrastructure, it provides a comprehensive architecture for reliable, reproducible test execution with proper resource limits and failure containment.

**Key Goals:**
- **Isolation:** Each test runs in a clean environment without shared state
- **Resource Control:** CPU, memory, and I/O limits prevent resource contention
- **Failure Containment:** One test failure doesn't crash the entire suite
- **Performance:** Minimize overhead while maintaining isolation guarantees
- **Reproducibility:** Identical behavior across development, CI, and production environments

---

## 1. Container Isolation Patterns

### 1.1 Individual Test Container Isolation

**Pattern:** Run each test file in a separate container with dedicated resources.

**Benefits:**
- Complete isolation - no shared state between tests
- Resource limits enforced at container level via cgroups
- Crash in one test doesn't affect others
- Easy to reproduce failures (just re-run that container)
- Security - tests run as non-root user in minimal environment

**Implementation:**
```bash
# Per-test container execution
docker run --rm \
  -v $(pwd):/workspace:ro \      # Read-only workspace
  --memory=128m \                 # Memory limit
  --cpus=0.5 \                    # CPU limit
  --network=none \                # No network access
  --read-only \                   # Read-only root filesystem
  --tmpfs /tmp:rw,noexec,nosuid \ # Writable /tmp, no executables
  --cap-drop=ALL \                # Drop all capabilities
  --security-opt=no-new-privileges \
  --user=1001:1001 \              # Non-root user
  simple-test-isolation:latest test/unit/test_file.spl
```

**Resource Limit Mechanisms:**

According to Docker documentation, resource constraints use Linux cgroups (control groups) to enforce limits:

- **Memory Limits:** Hard limits via `--memory` flag. When exceeded, kernel OOM killer terminates processes inside the container.
- **CPU Limits:** Pin containers to specific cores with `--cpuset-cpus`, or set relative weight with `--cpu-shares` (1024 = baseline).
- **I/O Limits:** Block device read/write limits via `--device-read-bps`, `--device-write-bps`, `--device-read-iops`, `--device-write-iops`.

**Current Simple Implementation:**

Simple already has a working container isolation setup:
- Docker image: `simple-test-isolation:latest` (~40MB, Alpine 3.18 + Simple runtime)
- Helper script: `scripts/local-container-test.sh`
- Documentation: `doc/guide/container_testing.md`

### 1.2 Container Resource Limits

**Best Practices (based on industry research):**

1. **Always Test Limits in Staging:** Understand your application's memory requirements before production.
2. **Security First:** Resource limits prevent DoS attacks - one container can't starve the host.
3. **Use Cgroups Properly:** Docker uses cgroups v1 or v2 (v2 preferred on modern Linux, unified hierarchy).
4. **Monitor Resource Usage:** Use `docker stats` to track actual usage and tune limits.

**Resource Profile Tiers (already implemented in Simple):**

| Profile | Memory | CPU | Timeout | Use Case |
|---------|--------|-----|---------|----------|
| **Fast** | 128 MB | 0.5 cores | 30s | Unit tests, pure logic |
| **Standard** | 512 MB | 1.0 cores | 120s | Integration tests, module interactions |
| **Slow** | 1 GB | 2.0 cores | 600s | System tests, full compilation |
| **Intensive** | 2 GB | 4.0 cores | 1800s | Heavy workloads, self-hosting builds |
| **Critical** | 4 GB | 8.0 cores | 3600s | QEMU, baremetal, cross-platform |

### 1.3 Volume Mounting Strategies

**Read-Only vs Read-Write:**

```bash
# Read-only (preferred for tests - prevents accidental modification)
-v $(pwd):/workspace:ro

# Read-write (needed if tests write to source tree)
-v $(pwd):/workspace:rw

# Best practice: read-only workspace + writable tmpfs
-v $(pwd):/workspace:ro --tmpfs /tmp:rw,size=512m
```

**Advantages of Read-Only Mounts:**
- Tests can't accidentally modify source code
- Forces explicit temporary file handling
- Prevents state leakage between test runs
- Matches CI environment (immutable source)

### 1.4 Container Cleanup Strategies

**Automatic Cleanup:**
```bash
# --rm flag removes container after exit
docker run --rm ...

# Named containers require manual cleanup
docker run --name test-1 ...  # Requires: docker rm test-1
```

**Resource Cleanup:**
```bash
# Clean up stopped containers
docker container prune -f

# Clean up unused images
docker image prune -a -f

# Clean up volumes (careful - may remove data)
docker volume prune -f

# Full cleanup (nuclear option)
docker system prune -a --volumes -f
```

**Best Practice:** Always use `--rm` for ephemeral test containers.

---

## 2. Process Isolation Patterns

### 2.1 Process-Based Isolation with ulimit

**Pattern:** Run tests in separate OS processes with resource limits enforced by the kernel.

**Benefits:**
- Lower overhead than containers (~100x faster startup)
- Native OS process isolation (namespaces, cgroups)
- Good for fast unit tests where full container isolation is overkill
- Works on systems without Docker/Podman

**Implementation:**
```bash
# Using ulimit and timeout
ulimit -v 131072 && \     # 128MB virtual memory limit
  ulimit -t 30 && \       # 30 second CPU time limit
  timeout 30s \           # Wall-clock timeout
  simple test test/unit/test_file.spl
```

**Linux-Specific (cgroups v2):**
```bash
# Create cgroup for test
cgcreate -g memory,cpu:test-runner

# Set limits
echo "134217728" > /sys/fs/cgroup/test-runner/memory.max    # 128MB
echo "50000 100000" > /sys/fs/cgroup/test-runner/cpu.max    # 50% of 1 CPU

# Run test in cgroup
cgexec -g memory,cpu:test-runner simple test test_file.spl

# Cleanup
cgdelete -g memory,cpu:test-runner
```

**Current Simple Implementation:**

Simple's parallel test runner (`src/app/test_runner_new/test_runner_parallel.spl`) uses `process_run_timeout()` for subprocess isolation:

```simple
fn run_subprocess(binary: text, file_path: text, options: TestOptions, timeout_ms: i64) -> TestFileResult:
    var args: [text] = [file_path, "--subprocess-mode"]
    val start = time_now_unix_micros()
    val result = process_run_timeout(binary, args, timeout_ms)
    val end = time_now_unix_micros()
    # Parse output and return result
```

**Limitation:** Sequential batching only - no true async parallel execution yet (requires `rt_process_spawn_async`).

### 2.2 CPU Affinity and Scheduling

**CPU Affinity (pinning tests to specific cores):**

```bash
# Run on CPU cores 0-1 only
taskset -c 0-1 simple test test_file.spl

# Run on specific core (no interference from other processes)
taskset -c 3 simple test test_file.spl
```

**Docker CPU Pinning:**
```bash
# Pin container to cores 0-1
docker run --cpuset-cpus="0-1" ...

# Pin to specific core
docker run --cpuset-cpus="3" ...
```

**Use Cases:**
- **NUMA-aware applications:** Pin to cores on same NUMA node
- **Performance-sensitive tests:** Isolate from system noise
- **Reproducible benchmarks:** Consistent CPU allocation

### 2.3 Memory Limits via Cgroups

**Cgroups v1 vs v2:**

According to research, cgroups v2 (unified hierarchy) is preferred on modern systems:
- **Cgroups v1:** Multiple hierarchies, complex management (deprecated)
- **Cgroups v2:** Single hierarchy, simplified management, consistent resource usage view

**Check Cgroups Version:**
```bash
mount | grep cgroup

# v1: Multiple mounts (memory, cpu, blkio, etc.)
# v2: Single mount at /sys/fs/cgroup
```

**Docker/Podman Automatically Use Cgroups:**
- `--memory=512m` → Sets `memory.max` in cgroup
- `--cpus=1.0` → Sets `cpu.max` in cgroup
- No manual cgroup management needed

### 2.4 Timeout Mechanisms

**Timeout Strategies:**

1. **Wall-Clock Timeout (preferred for tests):**
   ```bash
   timeout 30s simple test test_file.spl
   ```

2. **CPU Time Timeout (for CPU-bound tests):**
   ```bash
   ulimit -t 30  # 30 seconds of CPU time
   ```

3. **Combined (both limits):**
   ```bash
   ulimit -t 30 && timeout 60s simple test test_file.spl
   ```

**Docker Timeout:**
```bash
# Container-level timeout (requires separate timeout command)
timeout 30s docker run --rm ... simple-test-isolation:latest test file.spl

# Process timeout inside container
docker run --rm ... simple-test-isolation:latest test file.spl --timeout=30
```

**Simple's Timeout Implementation:**
- Per-test timeout: `timeout_ms` parameter in `process_run_timeout()`
- Profile-based defaults: 30s (fast), 120s (standard), 600s (slow)
- CLI override: `--timeout=600`

---

## 3. Test Runner Architecture

### 3.1 Sequential vs Parallel Execution

**Sequential Execution:**

```
Test 1 → Test 2 → Test 3 → Test 4
        (total time = sum of all tests)
```

**Benefits:**
- Simple to implement and debug
- Predictable resource usage
- No race conditions or concurrency bugs
- Deterministic output order

**Drawbacks:**
- Slow for large test suites
- Wastes CPU on multi-core systems
- Blocking - one slow test delays everything

**Parallel Execution:**

```
Worker 1: Test 1 → Test 5
Worker 2: Test 2 → Test 6
Worker 3: Test 3 → Test 7
Worker 4: Test 4 → Test 8
        (total time ≈ sum / worker_count)
```

**Benefits:**
- **Speed:** 1000 tests in 10 hours → 1 hour with 10 workers, or 30 minutes with 20 workers
- **Efficiency:** Utilizes multi-core CPUs
- **Modern:** Fits CI/CD pipelines (faster feedback)

**Drawbacks:**
- Higher resource usage (memory, file descriptors)
- More complex coordination and output aggregation
- Requires test independence (no shared state)

**Industry Research Findings:**

According to parallel testing guides from 2025-2026:
- Parallel execution reduces test time by ~1.5x compared to sequential (conservative)
- With proper distribution: 10 workers = ~10x speedup (linear scaling)
- Modern test runners use "sophisticated cloud-native solutions that scale elastically"
- Key requirement: "Standardizing environments, making tests independent, managing resources intelligently"

### 3.2 Resource Pool Management

**Worker Pool Pattern:**

```
Resource Pool (max N workers)
├─ Worker 1 (idle)
├─ Worker 2 (running test A)
├─ Worker 3 (running test B)
└─ Worker 4 (idle)

Queue: [test C, test D, test E, ...]
```

**Implementation Strategy:**

1. **Fixed Pool Size:** `max_workers = cpu_count() - 1` (leave 1 core free)
2. **Dynamic Scheduling:** Assign tests to idle workers as they complete
3. **Batch Processing:** Group small tests together, run large tests alone
4. **Priority Queue:** Fast tests first, slow tests last (minimizes tail latency)

**Simple's Current Implementation:**

```simple
fn run_tests_parallel(files: [text], options: TestOptions) -> [TestFileResult]:
    val config = ParallelConfig__from_options(options)
    var batch_start = 0

    # Process files in batches of max_workers
    while batch_start < files.len():
        val batch_end = min_i64(batch_start + config.max_workers, files.len())

        # Run batch (currently sequential, needs rt_process_spawn_async for true parallel)
        for i in batch_start..batch_end:
            val result = run_subprocess(binary, files[i], options, timeout_ms)
            results.push(result)
```

**Gap:** Needs async process spawning for true parallel execution.

### 3.3 Failure Isolation

**Pattern:** Test failures don't crash the entire suite.

**Research Findings:**

According to test isolation best practices:
- "Test isolation involves cleaning up state before each test to ensure that the operation of one test does not affect another test"
- "Tests that depend on the state of an earlier test can potentially cause nondeterministic test failures"
- "GoogleTest isolates tests by running each on a different object; when a test fails, you can run it in isolation for quick debugging"

**Failure Isolation Strategies:**

1. **Process-Level Isolation (preferred):**
   - Each test runs in separate process
   - Crash/segfault in test A doesn't kill test B
   - Exit code captures failure type (0 = pass, non-zero = fail, 137 = OOM kill)

2. **Container-Level Isolation (strongest):**
   - Each test runs in separate container
   - Complete filesystem/network isolation
   - Resource limits enforced by kernel

3. **Fail-Fast vs Continue-On-Error:**
   ```bash
   # Stop on first failure
   simple test --fail-fast

   # Run all tests, report all failures
   simple test
   ```

**Simple's Implementation:**
```simple
if options.fail_fast and (result.failed > 0 or result.timed_out):
    results.merge(batch_results)
    return results  # Early exit
```

### 3.4 Progress Reporting from Isolated Processes

**Challenge:** Tests run in separate processes/containers - how to aggregate output?

**Solutions:**

1. **Structured Output (JSON/XML):**
   ```json
   {
     "test_file": "test/unit/string_spec.spl",
     "passed": 42,
     "failed": 1,
     "skipped": 0,
     "duration_ms": 234
   }
   ```

2. **Simple's Approach (parse stdout):**
   ```simple
   fn parse_test_output(stdout: text) -> (i64, i64, i64, i64):
       # Parse "Passed: 42, Failed: 1, Skipped: 0"
   ```

3. **File-Based Reporting (JUnit XML):**
   ```xml
   <testsuite name="string_spec" tests="43" failures="1" time="0.234">
     <testcase name="trim removes whitespace" time="0.005"/>
     <testcase name="split on delimiter" time="0.003">
       <failure>Expected "a,b,c", got "a,b"</failure>
     </testcase>
   </testsuite>
   ```

**Best Practice:** Use structured output (JSON/XML) for machine parsing, pretty-printed output for humans.

---

## 4. Performance Considerations

### 4.1 Container Startup Overhead

**Research Findings:**

According to container performance benchmarks:
- **Containerd:** ~0.07 seconds startup time
- **Docker:** ~0.13 seconds startup time
- **Native execution:** ~0.001 seconds (100x faster)
- **CPU workload overhead:** Docker adds 0.56% latency compared to native

**Implications:**

For a test suite with 4,067 tests:
- **Native:** 4,067 × 4.3ms ≈ 17.5 seconds
- **Process isolation:** 4,067 × 5ms ≈ 20 seconds (15% overhead)
- **Container isolation:** 4,067 × (130ms + 4.3ms) ≈ 545 seconds (30x slowdown)

**Mitigation Strategies:**

1. **Batch Tests in Containers:** Group multiple test files per container
   ```bash
   docker run --rm ... test test/unit/*.spl  # Run all unit tests together
   ```

2. **Keep Containers Running:** Use long-lived containers with exec
   ```bash
   # Start container
   docker run -d --name test-runner simple-test-isolation:latest sleep infinity

   # Execute tests
   docker exec test-runner simple test test/unit/file1.spl
   docker exec test-runner simple test test/unit/file2.spl

   # Cleanup
   docker stop test-runner
   docker rm test-runner
   ```

3. **Use Container Pools:** Pre-start N containers, distribute tests across them

### 4.2 When to Use Process vs Container Isolation

**Decision Matrix:**

| Criterion | Process Isolation | Container Isolation |
|-----------|-------------------|---------------------|
| **Speed** | ✓✓✓ (100x faster startup) | ✗ (130ms overhead per container) |
| **Isolation** | ✓ (process namespaces) | ✓✓✓ (full OS-level isolation) |
| **Security** | ✓ (user-level isolation) | ✓✓✓ (no root, minimal capabilities) |
| **Reproducibility** | ✗ (depends on host OS) | ✓✓✓ (identical environment) |
| **Resource Limits** | ✓ (ulimit, cgroups) | ✓✓✓ (enforced by kernel) |
| **CI/CD** | ✗ (varies by runner) | ✓✓✓ (consistent everywhere) |

**Recommended Strategy:**

1. **Local Development:** Process isolation (fast iteration)
   ```bash
   simple test test/unit/  # Native execution
   ```

2. **Pre-Commit Verification:** Container isolation (matches CI)
   ```bash
   docker run --rm -v $(pwd):/workspace:ro ... test test/unit/changed_spec.spl
   ```

3. **CI/CD Pipeline:** Container isolation (reproducible)
   ```bash
   docker run --rm ... test  # Full suite in container
   ```

4. **Hybrid Approach:** Use both
   - Fast tests: Process isolation (unit tests, 4000+ tests)
   - Slow tests: Container isolation (integration/system tests, <100 tests)

### 4.3 Resource Limit Detection and Adaptive Scheduling

**Pattern:** Detect system resources and adjust parallelism dynamically.

**Implementation:**

```simple
# Already implemented in Simple
fn ParallelConfig__from_options(options: TestOptions) -> ParallelConfig:
    var max_workers = cpu_count()
    if max_workers < 1:
        max_workers = 1
    # Leave 1 core free for system
    if max_workers > 2:
        max_workers = max_workers - 1
```

**Advanced Strategies:**

1. **CPU Throttling (already in simple.test.sdn):**
   ```sdn
   cpu_throttle:
     enabled: true
     threshold: 70           # CPU usage % to trigger throttling
     memory_threshold: 70    # Memory usage % to trigger throttling
     throttled_threads: 1    # Drop to 1 thread when throttled
     check_interval: 5       # Check every 5 seconds
   ```

2. **Dynamic Resource Monitoring:**
   ```bash
   # Check available memory before starting tests
   available_mb=$(free -m | awk '/^Mem:/{print $7}')

   # Adjust container memory based on availability
   if [ $available_mb -lt 2048 ]; then
     memory_limit="128m"  # Low memory mode
   else
     memory_limit="512m"  # Normal mode
   fi

   docker run --memory=$memory_limit ...
   ```

3. **Adaptive Batch Sizing:**
   ```
   # High CPU usage → Reduce batch size
   if cpu_usage > 80%:
       batch_size = max_workers / 2

   # Low CPU usage → Increase batch size
   if cpu_usage < 40%:
       batch_size = max_workers * 2
   ```

**Research Finding:** "The higher the isolation of parallel tests, the smaller the likelihood of conflicts on shared state, but the higher the execution time and resources needed."

**Tradeoff:** More isolation = safer but slower; less isolation = faster but riskier.

---

## 5. Recommended Architecture

### 5.1 Three-Tier Test Execution Model

```
┌─────────────────────────────────────────────────────┐
│ CLI Entry Point (simple test)                       │
│ - Parse args, load config, detect runtime           │
└─────────────────┬───────────────────────────────────┘
                  │
                  ├─ Local Mode (--no-container)
                  │  └─► Tier 1: Native Process Isolation
                  │
                  ├─ Hybrid Mode (default)
                  │  ├─► Fast tests → Tier 1 (process)
                  │  └─► Slow tests → Tier 2 (container)
                  │
                  └─ Container Mode (--container)
                     └─► Tier 2: Container Isolation
                        └─► Tier 3: Nested Containers (CI/CD)
```

**Tier 1: Native Process Isolation**
- **Use:** Fast unit tests (<30s, <128MB)
- **Mechanism:** `process_run_timeout()` with ulimit
- **Overhead:** Minimal (~1ms per test)
- **Isolation:** Process-level (good for most cases)

**Tier 2: Container Isolation**
- **Use:** Integration/system tests, CI/CD verification
- **Mechanism:** Docker/Podman with resource limits
- **Overhead:** ~130ms per container startup
- **Isolation:** Full OS-level (cgroups, namespaces)

**Tier 3: Nested Containers (Advanced)**
- **Use:** Multi-tenant CI/CD (GitHub Actions, GitLab CI)
- **Mechanism:** Container inside container (requires `--privileged` or sysbox)
- **Overhead:** High (~500ms+)
- **Isolation:** Maximum (complete environment control)

### 5.2 Execution Flow Diagram

```
simple test <args>
    │
    ├─ Parse Arguments
    ├─ Load Config (simple.test.sdn)
    ├─ Discover Test Files
    ├─ Classify by Profile (fast/standard/slow/intensive/critical)
    │
    ├─ Sequential Mode (default)
    │   └─ For each test file:
    │       ├─ Select execution tier (process or container)
    │       ├─ Apply resource limits
    │       ├─ Run test
    │       ├─ Parse output
    │       ├─ Report result
    │       └─ Check fail-fast
    │
    └─ Parallel Mode (--parallel)
        ├─ Create worker pool (N = cpu_count - 1)
        ├─ Distribute tests across workers
        └─ For each worker:
            ├─ Select execution tier
            ├─ Apply resource limits
            ├─ Run test
            ├─ Parse output
            ├─ Report result (thread-safe aggregation)
            └─ Check fail-fast
```

### 5.3 Resource Profile Selection Logic

```
┌─ Test Discovery ─────────────────────────────────┐
│ 1. Scan test files (test/**/*_spec.spl)          │
│ 2. Extract tags (slow_it, intensive_it, etc.)    │
│ 3. Assign profile based on tag or default        │
└─────────────────┬─────────────────────────────────┘
                  │
┌─ Profile Assignment ─────────────────────────────┐
│ Test Tag → Profile Mapping:                      │
│ - it()          → fast (default)                 │
│ - slow_it()     → slow                           │
│ - intensive_it()→ intensive                      │
│ - critical_it() → critical                       │
└─────────────────┬─────────────────────────────────┘
                  │
┌─ Execution Tier Selection ───────────────────────┐
│ if --container: use Tier 2 (container)           │
│ elif profile == fast: use Tier 1 (process)       │
│ else: use Tier 2 (container)                     │
└─────────────────┬─────────────────────────────────┘
                  │
┌─ Resource Limit Application ─────────────────────┐
│ Apply limits from simple.test.sdn:               │
│ - Memory: profile.memory_mb                      │
│ - CPU: profile.cpu_cores                         │
│ - Timeout: profile.timeout_sec                   │
│ - I/O: profile.io_ops_per_sec (future)           │
└───────────────────────────────────────────────────┘
```

---

## 6. Container vs Process Isolation Tradeoffs

### 6.1 Performance Comparison

| Metric | Process Isolation | Container Isolation | Container with Pooling |
|--------|-------------------|---------------------|------------------------|
| **Startup Time** | 1-5ms | 70-130ms | 1-5ms (reuse) |
| **Memory Overhead** | Minimal (~1MB) | 10-40MB (image size) | 10-40MB (shared) |
| **CPU Overhead** | <0.1% | 0.5-1% | <0.1% (amortized) |
| **Disk I/O** | Native | 5-10% slower | Native (cached) |
| **Network I/O** | Native | 1-2% slower | Native |

**Benchmark Example (4,067 tests, 4.3ms avg):**

| Mode | Total Time | Overhead |
|------|------------|----------|
| Native | 17.5s | Baseline |
| Process Isolation | 20s | +15% |
| Container (per-test) | 545s | +3000% |
| Container (batched, 10 tests/container) | 70s | +300% |
| Container (pooled, 4 workers) | 25s | +45% |

**Conclusion:** Use container pooling or batching to reduce overhead.

### 6.2 Isolation Quality Comparison

| Isolation Aspect | Process | Container | Container + Seccomp |
|------------------|---------|-----------|---------------------|
| **Filesystem** | Shared | Isolated | Isolated |
| **Network** | Shared | Isolated (--network=none) | Isolated |
| **PID Namespace** | Shared | Isolated | Isolated |
| **IPC** | Shared | Isolated | Isolated |
| **User Namespace** | Shared | Isolated (--user) | Isolated |
| **Capabilities** | Full | Limited (--cap-drop=ALL) | Minimal |
| **Syscall Filtering** | None | None | Seccomp BPF |

**Research Finding:** "RunC and Kata Containers have less performance overhead, while gVisor suffers significant performance degradation in I/O and system calls, although its isolation is the best."

**Security Ranking:**
1. **gVisor** (maximum isolation, high overhead)
2. **Kata Containers** (VM-based, moderate overhead)
3. **RunC** (default Docker, low overhead)
4. **Process Isolation** (minimal overhead, basic isolation)

### 6.3 Reproducibility Comparison

| Scenario | Process Isolation | Container Isolation |
|----------|-------------------|---------------------|
| **Same Machine** | ✓ | ✓ |
| **Different OS Versions** | ✗ (libc differences) | ✓ (locked base image) |
| **Different Architectures** | ✗ (x86 ≠ ARM) | ✓ (multi-arch images) |
| **Developer → CI** | ✗ (env differences) | ✓ (same Dockerfile) |
| **CI → Production** | ✗ (runner differences) | ✓ (same image) |

**Best Practice:** Use containers for CI/CD, processes for local development.

---

## 7. Best Practices Summary

### 7.1 Development Workflow

```
┌─ Edit Code ──────────────────────────────────────┐
│ vim src/lib/text.spl                            │
└───────────────┬───────────────────────────────────┘
                │
┌─ Quick Test (Native) ────────────────────────────┐
│ bin/simple test test/unit/std/string_spec.spl    │
│ - Fastest iteration (<1s)                         │
│ - No isolation overhead                           │
└───────────────┬───────────────────────────────────┘
                │
┌─ Verify (Process Isolation) ─────────────────────┐
│ bin/simple test --parallel test/unit/std/        │
│ - Fast with basic isolation (~5s)                 │
│ - Catches most issues                             │
└───────────────┬───────────────────────────────────┘
                │
┌─ Pre-Commit (Container) ─────────────────────────┐
│ scripts/local-container-test.sh unit               │
│ - Full isolation (~30s)                           │
│ - Matches CI environment                          │
└───────────────┬───────────────────────────────────┘
                │
┌─ Push to CI ─────────────────────────────────────┐
│ git push                                          │
│ - GitHub Actions runs containerized tests         │
│ - Reproducible results                            │
└───────────────────────────────────────────────────┘
```

### 7.2 Test Classification Guidelines

**Fast Tests (Tier 1: Process Isolation):**
- Pure logic, no I/O
- <30s execution time
- <128MB memory usage
- No network access
- Examples: string operations, math, data structures

**Standard Tests (Tier 2: Container Isolation):**
- Module integration
- Small file I/O
- <120s execution time
- <512MB memory usage
- Examples: parser tests, small compilations

**Slow Tests (Tier 2: Container Isolation with higher limits):**
- Full compilation
- Large file processing
- <600s execution time
- <1GB memory usage
- Examples: compiler self-hosting, database migrations

**Critical Tests (Tier 2: Privileged Containers):**
- QEMU/KVM tests
- Baremetal boot
- Cross-platform builds
- <3600s execution time
- <4GB memory usage
- Examples: kernel boot tests, multi-arch builds

### 7.3 Resource Limit Tuning

**Start Conservative, Increase as Needed:**

1. **Measure First:**
   ```bash
   # Run with verbose output to see actual usage
   docker run --rm ... test --verbose test/unit/test_file.spl
   ```

2. **Profile Tests:**
   ```bash
   # Track peak memory
   docker stats simple-test

   # Check OOM kills
   dmesg | grep oom
   ```

3. **Adjust Limits:**
   ```sdn
   # In simple.test.sdn - increase memory if needed
   fast:
     memory_mb: 256  # Was 128, tests need more
   ```

4. **Document Rationale:**
   ```simple
   # In test file
   slow_it "compiles large project":
       # Note: Requires 1GB memory due to large AST (10,000+ nodes)
       compile("examples/large_project")
   ```

### 7.4 Failure Debugging Checklist

**Test Fails in CI but Passes Locally:**

1. **Run exact CI command locally:**
   ```bash
   docker run --rm -v $(pwd):/workspace:ro \
     --memory=512m --cpus=1.0 \
     --env CI=true \
     simple-test-isolation:latest test test/failing_spec.spl
   ```

2. **Check environment differences:**
   - Timezone (CI uses UTC)
   - Locale (CI uses en_US.UTF-8)
   - Environment variables (CI sets `CI=true`)

3. **Verify file permissions:**
   ```bash
   # CI mounts as read-only
   docker run --rm -v $(pwd):/workspace:ro ...
   # Local might mount as read-write
   ```

**Test Timeout:**

1. **Check profile:**
   ```bash
   # Is test tagged correctly?
   slow_it "long operation" vs it "long operation"
   ```

2. **Increase timeout:**
   ```bash
   docker run ... test --timeout=600 test/slow_spec.spl
   ```

3. **Optimize test:**
   - Use mocks instead of real operations
   - Split into smaller tests
   - Parallelize independent operations

**Out of Memory:**

1. **Check actual usage:**
   ```bash
   docker stats simple-test  # Real-time monitoring
   ```

2. **Increase limit or optimize:**
   ```bash
   # Temporary: increase limit
   docker run --memory=1g ...

   # Permanent: optimize test (reduce allocations)
   ```

3. **Check for leaks:**
   - Run test multiple times
   - Compare memory usage between runs
   - Profile with valgrind/heaptrack

---

## 8. Conclusion and Key Recommendations

### 8.1 Key Takeaways

1. **Container Isolation is Best for Reproducibility:**
   - Same environment everywhere (dev, CI, production)
   - Resource limits enforced by kernel (cgroups)
   - Maximum security (no root, minimal capabilities)

2. **Process Isolation is Best for Performance:**
   - 100x faster startup than containers
   - Minimal overhead (<1% CPU)
   - Good enough for most unit tests

3. **Hybrid Approach is Optimal:**
   - Fast tests → Process isolation (4000+ tests, <30s)
   - Slow tests → Container isolation (100 tests, >30s)
   - CI/CD → Full container isolation (reproducibility)

4. **Resource Limits Prevent Problems:**
   - Memory limits catch leaks early
   - CPU limits prevent runaway tests
   - Timeouts ensure suite completion

5. **Failure Isolation is Critical:**
   - One test crash shouldn't kill entire suite
   - Process/container isolation provides this automatically
   - Fail-fast mode for quick feedback

### 8.2 Recommended Next Steps for Simple Language

**Immediate:**
- Enhance `test_runner_parallel.spl` with ulimit enforcement
- Add structured JSON output for better parsing
- Improve resource usage tracking

**Short-Term:**
- Implement container pool management for reduced overhead
- Add automatic health checks and restart
- Create work-stealing queue for better load balancing

**Medium-Term:**
- Build hybrid execution engine (auto-select tier)
- Add test profiler to classify tests
- Implement tier-specific optimizations

**Long-Term:**
- Real-time resource monitoring with `resource_tracker.spl`
- Adaptive throttling based on system load
- Resource usage dashboards and reports

---

## Sources

This research drew from the following sources:

**Container Resource Management:**
- [Docker CPU & Memory Limits: Prevent Container Resource Exhaustion](https://oneuptime.com/blog/post/2026-01-16-docker-limit-cpu-memory/view)
- [Resource constraints | Docker Docs](https://docs.docker.com/engine/containers/resource_constraints/)
- [How to Set Up Docker Container Resource Constraints](https://oneuptime.com/blog/post/2026-01-25-docker-container-resource-constraints/view)
- [Optimizing Docker Container Performance: Best Practices for Resource Allocation](https://loadforge.com/guides/best-practices-for-docker-container-resource-allocation)
- [How to Limit Docker Memory and CPU Usage | phoenixNAP KB](https://phoenixnap.com/kb/docker-memory-and-cpu-limit)

**Process Isolation and Cgroups:**
- [Cgroup Resource Isolation Tests](https://medium.com/@eren.c.uysal/cgroup-resource-isolation-tests-5aa8a58f733b)
- [How Docker Containers Work Under the Hood: Namespaces and Cgroups](https://www.atlantbh.com/how-docker-containers-work-under-the-hood-namespaces-and-cgroups/)
- [Everything You Need to Know about Linux Containers, Part I: Linux Control Groups and Process Isolation](https://www.linuxjournal.com/content/everything-you-need-know-about-linux-containers-part-i-linux-control-groups-and-process)
- [Exploring Cgroups v1 and Cgroups v2: Understanding the Evolution of Resource Control](https://dohost.us/index.php/2025/10/11/exploring-cgroups-v1-and-cgroups-v2-understanding-the-evolution-of-resource-control/)

**Container vs Process Performance:**
- [Docker Bootcamp - Container Isolation Modes / Blogs / Perficient](https://blogs.perficient.com/2022/10/10/docker-bootcamp-container-isolation-modes/)
- [VMs & Container: Performance and Isolation Comparison](https://medium.com/@27krishna2002/vms-container-performance-and-isolation-comparison-c76b071621ba)
- [Understanding the performance of container execution environments](https://www.researchgate.net/publication/348414147_Understanding_the_performance_of_container_execution_environments)
- [Understanding Container Isolation | Proceedings of the 9th International Workshop on Container Technologies and Container Clouds](https://dl.acm.org/doi/10.1145/3631311.3632400)

**Container Performance Benchmarks:**
- [Edera Performance Benchmarks: Security Without Sacrifice](https://edera.dev/stories/security-without-sacrifice-edera-performance-benchmarking)
- [System Container Performance Analysis | Nestybox Blog Site](https://blog.nestybox.com/2020/09/23/perf-comparison.html)
- [Benchmarking containerd vs. dockerd: Performance, Efficiency, and Scalability](https://medium.com/norma-dev/benchmarking-containerd-vs-dockerd-performance-efficiency-and-scalability-64c9043924b1)

**Parallel Test Execution:**
- [Parallel Testing in Software Testing | Expert Guide 2026](https://www.accelq.com/blog/parallel-testing/)
- [Parallel Test Execution for 10x Faster Testing](https://www.virtuosoqa.com/post/parallel-test-execution)
- [Parallel Test Execution Guide](https://blog.testery.io/parallel-test-execution-guide/)
- [Running Tests in Parallel | xUnit.net](https://xunit.net/docs/running-tests-in-parallel)

**Test Isolation Best Practices:**
- [Test Isolation as a Best Practice](https://www.cypress.io/blog/test-isolation-as-a-best-practice)
- [Test Isolation, and "Listening to Your Tests"](https://www.obeythetestinggoat.com/book/appendix_purist_unit_tests.html)
- [Unit Tests Are FIRST: Fast, Isolated, Repeatable, Self-Verifying, and Timely](https://medium.com/pragmatic-programmers/unit-tests-are-first-fast-isolated-repeatable-self-verifying-and-timely-a83e8070698e)
- [GoogleTest Primer | GoogleTest](http://google.github.io/googletest/primer.html)

---

**Document Version:** 1.0
**Last Updated:** 2026-02-14
**Author:** Claude Code (docs agent)
**Review Status:** Ready for reference
