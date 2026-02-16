# Container-Based Testing Guide

## Overview

Container-based testing provides isolated, reproducible test execution environments for the Simple language test suite. Tests run in minimal containers with controlled resource limits, ensuring consistency across development machines and CI/CD pipelines.

**Benefits:**
- **Isolation:** Each test runs in a fresh environment with no shared state
- **Reproducibility:** Identical environment across machines (local, CI, production)
- **Resource Control:** CPU, memory, and I/O limits prevent resource contention
- **Security:** Tests run as non-root user with minimal capabilities
- **Debugging:** Easy reproduction of CI failures locally

**Container Size:** ~40MB (Alpine 3.18 + Simple runtime)

---

## Quick Start

### Prerequisites

Install either Docker or Podman:

```bash
# Docker (recommended for beginners)
sudo apt install docker.io      # Ubuntu/Debian
brew install docker             # macOS

# Podman (recommended for rootless execution)
sudo apt install podman         # Ubuntu/Debian
brew install podman             # macOS
```

### Build Test Container

```bash
# Using Docker
docker build -t simple-test-isolation:latest -f docker/Dockerfile.test-isolation .

# Using Podman
podman build -t simple-test-isolation:latest -f docker/Dockerfile.test-isolation .
```

### Run Tests

```bash
# Run all tests
docker run --rm -v $(pwd):/workspace:ro \
  --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test

# Run specific test file
docker run --rm -v $(pwd):/workspace:ro \
  --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test test/unit/std/string_spec.spl

# Run with verbose output
docker run --rm -v $(pwd):/workspace:ro \
  --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test --verbose test/unit/

# List available tests
docker run --rm -v $(pwd):/workspace:ro \
  simple-test-isolation:latest test --list
```

---

## Local Development Workflow

### 1. Edit Code

Make changes to Simple source files or test specs:

```bash
# Edit source
vim src/std/text.spl

# Edit test
vim test/unit/std/string_spec.spl
```

### 2. Run Tests Locally (Fast)

For quick iteration, run tests directly without containers:

```bash
# Fast local test (no isolation)
bin/simple test test/unit/std/string_spec.spl
```

### 3. Run Tests in Container (Verification)

Before committing, verify in isolated environment:

```bash
# Container test (matches CI environment)
docker run --rm -v $(pwd):/workspace:ro \
  --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test test/unit/std/string_spec.spl
```

### 4. Run Full Test Suite

```bash
# All unit tests (fast tier)
docker run --rm -v $(pwd):/workspace:ro \
  --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test test/unit/

# All integration tests (standard tier)
docker run --rm -v $(pwd):/workspace:ro \
  --memory=1g --cpus=2.0 \
  simple-test-isolation:latest test test/integration/

# All system tests (slow tier)
docker run --rm -v $(pwd):/workspace:ro \
  --memory=2g --cpus=4.0 \
  simple-test-isolation:latest test test/system/
```

---

## Resource Profile Configuration

Tests are categorized by resource requirements. Configure limits in `simple.test.sdn`:

```sdn
test:
  # Resource profiles (per-test limits)
  resource_profiles:
    fast:
      memory_mb: 128
      cpu_cores: 0.5
      timeout_sec: 30
      io_ops_per_sec: 1000

    standard:
      memory_mb: 512
      cpu_cores: 1.0
      timeout_sec: 120
      io_ops_per_sec: 5000

    slow:
      memory_mb: 1024
      cpu_cores: 2.0
      timeout_sec: 600
      io_ops_per_sec: 10000

    intensive:
      memory_mb: 2048
      cpu_cores: 4.0
      timeout_sec: 1800
      io_ops_per_sec: 50000

    critical:
      memory_mb: 4096
      cpu_cores: 8.0
      timeout_sec: 3600
      io_ops_per_sec: 100000
```

### Assigning Profiles to Tests

Tag tests in spec files:

```simple
# Fast test (default - most unit tests)
describe "String.trim":
  it "removes leading whitespace":
    expect("  hello".trim()).to_equal("hello")

# Slow test (integration/system tests)
slow_it "compiles large file":
  val result = compile("examples/large_app.spl")
  expect(result.?).to_equal(true)

# Critical test (baremetal, QEMU, cross-platform)
critical_it "boots on RISC-V baremetal":
  val result = run_qemu_riscv("bin/kernel.elf")
  expect(result.exit_code).to_equal(0)
```

### CLI Override

Override profile at runtime:

```bash
# Force slow profile for all tests
docker run --rm -v $(pwd):/workspace:ro \
  --memory=1g --cpus=2.0 \
  simple-test-isolation:latest test --profile=slow

# Run only fast tests
docker run --rm -v $(pwd):/workspace:ro \
  --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test --only-fast

# Run only slow tests (CI scheduled builds)
docker run --rm -v $(pwd):/workspace:ro \
  --memory=2g --cpus=4.0 \
  simple-test-isolation:latest test --only-slow
```

---

## Container Runtime Options

### Docker vs Podman

**Docker:**
- Industry standard, widest compatibility
- Requires daemon, typically needs sudo
- Better Windows/macOS support

**Podman:**
- Rootless execution (no sudo required)
- Drop-in Docker replacement
- Better Linux security model

Both work identically for Simple tests. Use `--container-runtime` flag:

```bash
# Use Docker (default)
bin/simple test --container --container-runtime=docker

# Use Podman
bin/simple test --container --container-runtime=podman

# Auto-detect (tries podman, falls back to docker)
bin/simple test --container --container-runtime=auto
```

### Security Hardening

Containers run with minimal privileges:

```bash
# Default security options (applied automatically)
docker run --rm \
  -v $(pwd):/workspace:ro \         # Read-only workspace
  --read-only \                      # Read-only root filesystem
  --tmpfs /tmp:rw,noexec,nosuid \    # Writable /tmp, no executables
  --cap-drop=ALL \                   # Drop all capabilities
  --security-opt=no-new-privileges \ # Prevent privilege escalation
  --user=1001:1001 \                 # Non-root user
  simple-test-isolation:latest test
```

Add specific capabilities if needed:

```bash
# Network tests (require CAP_NET_RAW for raw sockets)
docker run --rm -v $(pwd):/workspace:ro \
  --cap-add=NET_RAW \
  simple-test-isolation:latest test test/network/
```

---

## Troubleshooting

### Container Build Fails

**Problem:** `docker build` fails with "no such file or directory"

**Solution:** Ensure you're in project root and runtime exists:

```bash
# Check current directory
pwd  # Should be /path/to/simple

# Check runtime exists
ls -lh bin/release/simple  # Should be ~33MB

# If missing, download or build runtime
scripts/install.sh
```

### Permission Denied

**Problem:** Container can't read workspace files

**Solution:** Fix file permissions:

```bash
# Make workspace readable
chmod -R a+rX .

# Or run container as current user
docker run --rm -v $(pwd):/workspace:ro \
  --user=$(id -u):$(id -g) \
  simple-test-isolation:latest test
```

### Out of Memory

**Problem:** Tests fail with "killed" or OOM errors

**Solution:** Increase memory limit:

```bash
# Check test profile requirement (simple.test.sdn)
cat simple.test.sdn | grep -A 5 "slow:"

# Increase Docker memory
docker run --rm -v $(pwd):/workspace:ro \
  --memory=2g \  # Was 512m, now 2g
  simple-test-isolation:latest test test/slow_spec.spl
```

### Timeout Errors

**Problem:** Tests timeout before completion

**Solution:** Increase timeout or use correct profile:

```bash
# Override timeout (seconds)
docker run --rm -v $(pwd):/workspace:ro \
  --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test --timeout=600 test/integration/

# Use slow profile (10 minute timeout)
docker run --rm -v $(pwd):/workspace:ro \
  --memory=1g --cpus=2.0 \
  simple-test-isolation:latest test --profile=slow
```

### Volume Mount Not Working

**Problem:** Container doesn't see local changes

**Solution:** Check Docker volume mount syntax:

```bash
# Linux/macOS
docker run --rm -v $(pwd):/workspace:ro ...

# Windows PowerShell
docker run --rm -v ${PWD}:/workspace:ro ...

# Windows CMD
docker run --rm -v %cd%:/workspace:ro ...
```

### Container Registry Issues

**Problem:** Can't pull base image (Alpine)

**Solution:** Configure Docker registry mirror or use cache:

```bash
# Use Docker Hub mirror
docker build --build-arg BASE_IMAGE=docker.io/library/alpine:3.18 \
  -t simple-test-isolation:latest -f docker/Dockerfile.test-isolation .

# Pull base image explicitly first
docker pull alpine:3.18
docker build -t simple-test-isolation:latest -f docker/Dockerfile.test-isolation .
```

### CI vs Local Mismatch

**Problem:** Tests pass locally but fail in CI

**Solution:** Run exact CI configuration locally:

```bash
# Check CI workflow for exact command
cat .github/workflows/containerized-tests.yml

# Copy Docker run command from workflow
docker run --rm -v $(pwd):/workspace:ro \
  --memory=512m --cpus=1.0 \
  --env CI=true \
  simple-test-isolation:latest test test/unit/
```

---

## Advanced Usage

### Parallel Test Execution

Run multiple containers in parallel:

```bash
# Start 4 parallel test runners
for i in {1..4}; do
  docker run --rm -v $(pwd):/workspace:ro \
    --memory=512m --cpus=1.0 \
    --name simple-test-$i \
    simple-test-isolation:latest test --parallel --shard=$i/4 &
done

# Wait for all to complete
wait
```

### Custom Test Environment

Override environment variables:

```bash
# Set custom runtime mode
docker run --rm -v $(pwd):/workspace:ro \
  --env SIMPLE_RUNTIME_MODE=compiled \
  simple-test-isolation:latest test

# Debug mode
docker run --rm -v $(pwd):/workspace:ro \
  --env SIMPLE_DEBUG=1 \
  simple-test-isolation:latest test --verbose
```

### Interactive Debugging

Drop into shell for debugging:

```bash
# Interactive bash shell
docker run -it --rm -v $(pwd):/workspace \
  --entrypoint /bin/bash \
  simple-test-isolation:latest

# Inside container:
simple test test/unit/failing_spec.spl --verbose
simple -c "use std.text.{trim}; print trim(\"  hello  \")"
```

### Build Cache Optimization

Speed up repeated builds:

```bash
# Enable BuildKit (faster builds)
export DOCKER_BUILDKIT=1

# Cache intermediate layers
docker build --cache-from simple-test-isolation:latest \
  -t simple-test-isolation:latest \
  -f docker/Dockerfile.test-isolation .
```

---

## See Also

- **Resource Limits Guide:** `doc/guide/resource_limits.md`
- **Test Configuration:** `simple.test.sdn`
- **CI/CD Integration:** `.github/workflows/containerized-tests.yml`
- **Test Writing Guide:** `doc/guide/test.md`
- **Isolation Testing:** `docker/Dockerfile.test-isolation`
