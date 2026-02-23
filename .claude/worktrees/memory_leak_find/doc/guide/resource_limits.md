# Resource Limits and Test Profiles

## Overview

Resource limits ensure tests run efficiently and predictably across environments. Tests are categorized into resource profiles that define memory, CPU, timeout, and I/O constraints.

**Why Resource Limits?**
- **Prevent resource contention:** Multiple tests don't compete for system resources
- **Reproducible performance:** Tests run consistently across machines
- **Early detection:** Memory leaks and performance regressions caught quickly
- **Fair scheduling:** Fast tests don't wait behind slow tests

---

## Resource Profile Tiers

### Fast (Default - Unit Tests)

**Use for:** Pure logic, string operations, math, small data structures

**Limits:**
- Memory: 128 MB
- CPU: 0.5 cores
- Timeout: 30 seconds
- I/O: 1,000 ops/sec

**Examples:**
```simple
describe "String.trim":
  it "removes whitespace":
    expect("  hello  ".trim()).to_equal("hello")

describe "Math.sqrt":
  it "calculates square root":
    expect(Math.sqrt(16.0)).to_equal(4.0)
```

**Container command:**
```bash
docker run --rm -v $(pwd):/workspace:ro \
  --memory=128m --cpus=0.5 \
  simple-test-isolation:latest test test/unit/
```

---

### Standard (Integration Tests)

**Use for:** Module integration, small file I/O, basic compilation

**Limits:**
- Memory: 512 MB
- CPU: 1.0 cores
- Timeout: 120 seconds (2 minutes)
- I/O: 5,000 ops/sec

**Examples:**
```simple
describe "Compiler.parse":
  it "parses simple module":
    val ast = parse("fn main(): print 42")
    expect(ast.?).to_equal(true)

describe "FileSystem.read":
  it "reads small file":
    val content = file_read("test/fixtures/sample.txt")
    expect(content.len()).to_be_greater_than(0)
```

**Container command:**
```bash
docker run --rm -v $(pwd):/workspace:ro \
  --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test test/integration/
```

---

### Slow (System Tests)

**Use for:** Full compilation, large file processing, database operations

**Limits:**
- Memory: 1,024 MB (1 GB)
- CPU: 2.0 cores
- Timeout: 600 seconds (10 minutes)
- I/O: 10,000 ops/sec

**Examples:**
```simple
describe "Compiler.build":
  slow_it "compiles full project":
    val result = compile_project("examples/web_server")
    expect(result.?).to_equal(true)
    expect(file_exists("examples/web_server/bin/server")).to_equal(true)

describe "Database.migrate":
  slow_it "runs all migrations":
    val db = Database.connect("test.db")
    val result = db.migrate_all()
    expect(result.errors.len()).to_equal(0)
```

**Container command:**
```bash
docker run --rm -v $(pwd):/workspace:ro \
  --memory=1g --cpus=2.0 \
  simple-test-isolation:latest test test/system/ --only-slow
```

---

### Intensive (Heavy Workloads)

**Use for:** Multi-file compilation, complex code generation, performance tests

**Limits:**
- Memory: 2,048 MB (2 GB)
- CPU: 4.0 cores
- Timeout: 1,800 seconds (30 minutes)
- I/O: 50,000 ops/sec

**Examples:**
```simple
describe "NativeBackend.compile":
  intensive_it "compiles compiler self-hosting":
    val result = compile_native("src/compiler/")
    expect(result.?).to_equal(true)
    expect(file_size("bin/compiler") > 1000000).to_equal(true)

describe "Performance.benchmark":
  intensive_it "runs full benchmark suite":
    val results = run_benchmarks("bench/")
    expect(results.len()).to_be_greater_than(100)
```

**Container command:**
```bash
docker run --rm -v $(pwd):/workspace:ro \
  --memory=2g --cpus=4.0 \
  simple-test-isolation:latest test --profile=intensive
```

---

### Critical (Baremetal, QEMU, Cross-Platform)

**Use for:** QEMU VM tests, baremetal boot, multi-platform builds

**Limits:**
- Memory: 4,096 MB (4 GB)
- CPU: 8.0 cores
- Timeout: 3,600 seconds (1 hour)
- I/O: 100,000 ops/sec

**Examples:**
```simple
describe "Baremetal.boot":
  critical_it "boots on RISC-V QEMU":
    val qemu = start_qemu_riscv("bin/kernel.elf")
    val output = qemu.wait_for_output("Kernel initialized", timeout: 60)
    expect(output.?).to_equal(true)
    qemu.shutdown()

describe "CrossCompile.windows":
  critical_it "builds Windows binary from Linux":
    val result = cross_compile("windows-x86_64", "src/app/cli/")
    expect(result.?).to_equal(true)
    expect(file_exists("bin/simple.exe")).to_equal(true)
```

**Container command:**
```bash
docker run --rm -v $(pwd):/workspace:ro \
  --memory=4g --cpus=8.0 --privileged \
  simple-test-isolation:latest test --profile=critical
```

**Note:** Critical tests often require `--privileged` for QEMU/KVM access.

---

## Configuring Resource Limits

### Global Configuration (simple.test.sdn)

Define resource profiles in project config:

```sdn
test:
  # Resource profiles (container limits per test)
  resource_profiles:
    fast:
      memory_mb: 128
      cpu_cores: 0.5
      timeout_sec: 30
      io_ops_per_sec: 1000
      description: "Unit tests - pure logic, no I/O"

    standard:
      memory_mb: 512
      cpu_cores: 1.0
      timeout_sec: 120
      io_ops_per_sec: 5000
      description: "Integration tests - module interactions"

    slow:
      memory_mb: 1024
      cpu_cores: 2.0
      timeout_sec: 600
      io_ops_per_sec: 10000
      description: "System tests - full compilation"

    intensive:
      memory_mb: 2048
      cpu_cores: 4.0
      timeout_sec: 1800
      io_ops_per_sec: 50000
      description: "Heavy workloads - self-hosting builds"

    critical:
      memory_mb: 4096
      cpu_cores: 8.0
      timeout_sec: 3600
      io_ops_per_sec: 100000
      description: "QEMU, baremetal, cross-platform"

  # Default profile for tests without explicit tags
  default_profile: fast

  # Profile selection (override via CLI)
  profile: fast  # fast, standard, slow, intensive, critical
```

### Per-Test Tagging

Tag tests with resource requirements:

```simple
# Fast (default - no tag needed)
describe "String operations":
  it "concatenates strings":
    expect("hello " + "world").to_equal("hello world")

# Slow
describe "File compilation":
  slow_it "compiles large file":
    compile("examples/large.spl")

# Intensive
describe "Compiler self-hosting":
  intensive_it "builds full compiler":
    compile_all("src/compiler/")

# Critical
describe "QEMU testing":
  critical_it "runs on ARM64 QEMU":
    run_qemu_arm64("bin/kernel.elf")
```

### CLI Override

Override profile at runtime:

```bash
# Run with specific profile
bin/simple test --profile=slow test/integration/

# Run only tests matching profile
bin/simple test --only-fast      # Fast tests only
bin/simple test --only-slow      # Slow tests only
bin/simple test --only-intensive # Intensive tests only
bin/simple test --only-critical  # Critical tests only

# Override memory limit
bin/simple test --memory=2048 test/system/

# Override timeout
bin/simple test --timeout=600 test/slow_spec.spl
```

---

## Platform-Specific Considerations

### Linux

**Native execution:** Tests run directly on host (fastest)

```bash
# Direct execution (no container)
bin/simple test test/unit/

# Container isolation
docker run --rm -v $(pwd):/workspace:ro \
  --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test
```

**cgroups v2:** Modern Linux uses cgroups v2 for resource control:

```bash
# Check cgroups version
mount | grep cgroup

# cgroups v1 (older systems)
--memory=512m --cpus=1.0

# cgroups v2 (Ubuntu 22.04+, Fedora 31+)
--memory=512m --cpus=1.0  # Same syntax, better enforcement
```

---

### macOS

**Docker Desktop:** Uses VM (adds overhead ~10-20%)

```bash
# Adjust limits for VM overhead
docker run --rm -v $(pwd):/workspace:ro \
  --memory=640m --cpus=1.2 \  # 20% higher than Linux
  simple-test-isolation:latest test
```

**Podman:** Requires Podman Machine VM

```bash
# Initialize Podman VM (once)
podman machine init --memory=4096 --cpus=4

# Start VM
podman machine start

# Run tests (same syntax as Docker)
podman run --rm -v $(pwd):/workspace:ro \
  --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test
```

---

### Windows

**Docker Desktop (WSL2):** Runs in WSL2 VM

```bash
# PowerShell (note: forward slashes in paths)
docker run --rm -v ${PWD}:/workspace:ro `
  --memory=512m --cpus=1.0 `
  simple-test-isolation:latest test

# CMD
docker run --rm -v %cd%:/workspace:ro ^
  --memory=512m --cpus=1.0 ^
  simple-test-isolation:latest test
```

**Resource allocation:** Configure in Docker Desktop settings:
1. Open Docker Desktop
2. Settings → Resources
3. Set Memory: 4 GB minimum (8 GB recommended)
4. Set CPUs: 4 cores minimum

---

### FreeBSD

**Native execution:** Simple runtime runs via Linuxulator

```bash
# Enable Linux compatibility
sysctl kern.elf64.fallback_brand=Linux

# Install Linux base
pkg install linux_base-c7

# Run tests directly
bin/release/simple test test/unit/
```

**Container support:** Use FreeBSD jails instead of Docker

```bash
# Create jail (similar to containers)
jail -c name=simple-test path=/jails/simple \
  mount.devfs \
  host.hostname=simple-test \
  ip4.addr=10.0.0.2 \
  exec.start="/bin/sh /etc/rc" \
  exec.stop="/bin/sh /etc/rc.shutdown"

# Run tests in jail
jexec simple-test /workspace/bin/simple test
```

---

## Resource Limit Enforcement

### Memory Limits

**Soft limit:** Warning when exceeded
**Hard limit:** Process killed (OOM)

```bash
# Set soft and hard limits
docker run --rm -v $(pwd):/workspace:ro \
  --memory=512m \           # Hard limit
  --memory-reservation=256m \ # Soft limit (warning)
  simple-test-isolation:latest test
```

**Detecting OOM:**
```bash
# Check container exit code
docker ps -a --filter "name=simple-test" --format "{{.Status}}"
# Output: Exited (137) - killed by OOM

# Check system logs
dmesg | grep oom
journalctl -k | grep oom
```

### CPU Limits

**CPU shares:** Relative weight (default: 1024)
**CPU quota:** Hard cap (microseconds per 100ms)

```bash
# Limit to 50% of 1 CPU (0.5 cores)
docker run --rm -v $(pwd):/workspace:ro \
  --cpus=0.5 \
  simple-test-isolation:latest test

# Alternative: CPU quota
docker run --rm -v $(pwd):/workspace:ro \
  --cpu-period=100000 \    # 100ms
  --cpu-quota=50000 \      # 50ms (50% of 1 core)
  simple-test-isolation:latest test
```

### I/O Limits

**Block I/O weight:** Relative priority (10-1000)
**Device read/write limits:** Bytes or ops per second

```bash
# Limit disk I/O to 10 MB/s reads, 5 MB/s writes
docker run --rm -v $(pwd):/workspace:ro \
  --device-read-bps /dev/sda:10mb \
  --device-write-bps /dev/sda:5mb \
  simple-test-isolation:latest test

# Limit I/O ops per second
docker run --rm -v $(pwd):/workspace:ro \
  --device-read-iops /dev/sda:1000 \
  --device-write-iops /dev/sda:500 \
  simple-test-isolation:latest test
```

---

## Monitoring Resource Usage

### During Test Execution

```bash
# Real-time stats (separate terminal)
docker stats simple-test

# Output:
# CONTAINER    CPU %    MEM USAGE/LIMIT    MEM %    NET I/O    BLOCK I/O
# simple-test  45.2%    234MB / 512MB      45.7%    0B/0B      1.2MB/0B
```

### Post-Execution Analysis

```bash
# Container inspect (after test completes)
docker inspect simple-test | jq '.[0].HostConfig.Memory'
docker inspect simple-test | jq '.[0].HostConfig.CpuQuota'

# Container logs with stats
docker logs --timestamps simple-test
```

### CI/CD Metrics

GitHub Actions provides resource usage in workflow logs:

```yaml
# .github/workflows/containerized-tests.yml
- name: Run tests with monitoring
  run: |
    docker run --name simple-test -v $(pwd):/workspace:ro \
      --memory=512m --cpus=1.0 \
      simple-test-isolation:latest test

    # Capture stats after completion
    docker stats --no-stream simple-test
```

---

## Troubleshooting

### Test Fails Due to Memory Limit

**Symptom:** Process killed, exit code 137

**Solution:** Increase memory or optimize test

```bash
# Temporary fix: increase limit
docker run --memory=1g ...

# Permanent fix: optimize test (reduce allocations)
# Or tag test as 'slow' or 'intensive'
```

### Test Timeout

**Symptom:** Killed after timeout period

**Solution:** Tag test with appropriate profile

```simple
# Before (fast profile, 30s timeout - fails)
describe "Slow compilation":
  it "compiles large file":
    compile("large.spl")  # Takes 5 minutes

# After (slow profile, 10min timeout - passes)
describe "Slow compilation":
  slow_it "compiles large file":
    compile("large.spl")
```

### CPU Throttling

**Symptom:** Tests run slower than expected

**Solution:** Check system load, increase CPU quota

```bash
# Check host CPU usage
top

# Increase container CPU allocation
docker run --cpus=2.0 ...  # Was 1.0, now 2.0
```

### I/O Bottleneck

**Symptom:** Disk-heavy tests timeout

**Solution:** Use tmpfs for temporary files

```bash
# Mount /tmp as tmpfs (in-memory)
docker run --tmpfs /tmp:rw,size=512m ...
```

---

## Best Practices

1. **Start with fast profile:** Default all tests to fast, only promote when necessary
2. **Measure before promoting:** Use `--verbose` to see actual resource usage
3. **Isolate slow operations:** Extract slow parts into separate test files
4. **Use mocks for I/O:** Mock file/network operations in unit tests
5. **Clean up resources:** Close files, connections in `after_each` hooks
6. **Profile regularly:** Run `--profile=all` monthly to detect regressions
7. **Document assumptions:** Note why a test needs intensive/critical profile

---

## See Also

- **Container Testing Guide:** `doc/guide/container_testing.md`
- **Test Configuration:** `simple.test.sdn`
- **Test Writing:** `doc/guide/test.md`
- **CI/CD Integration:** `.github/workflows/containerized-tests.yml`
