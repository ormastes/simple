# Container-Based Testing Guide

Isolated, reproducible test execution using containers with controlled resource limits.

---

## Table of Contents

1. [Overview](#overview)
2. [Quick Start](#quick-start)
3. [Local Development Workflow](#local-development-workflow)
4. [Resource Profiles](#resource-profiles)
5. [Container Runtime Options](#container-runtime-options)
6. [Helper Scripts](#helper-scripts)
7. [Docker Compose](#docker-compose)
8. [Security Hardening](#security-hardening)
9. [Platform Considerations](#platform-considerations)
10. [Troubleshooting](#troubleshooting)

---

## Overview

Container-based testing provides:

- **Isolation** -- Each test runs in a fresh environment with no shared state
- **Reproducibility** -- Identical environment across machines (local, CI, production)
- **Resource Control** -- CPU, memory, and I/O limits prevent resource contention
- **Security** -- Tests run as non-root user with minimal capabilities
- **Debugging** -- Easy reproduction of CI failures locally

Container size: ~40MB (Alpine 3.18 + Simple runtime).

---

## Quick Start

### Prerequisites

Install Docker or Podman:

```bash
# Docker
brew install docker             # macOS
sudo apt install docker.io      # Ubuntu/Debian

# Podman (rootless alternative)
brew install podman             # macOS
sudo apt install podman         # Ubuntu/Debian
```

### Build and Run

```bash
# Build test container
docker build -t simple-test-isolation:latest -f docker/Dockerfile.test-isolation .

# Run all tests
docker run --rm -v $(pwd):/workspace:ro \
  --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test

# Run specific test file
docker run --rm -v $(pwd):/workspace:ro \
  --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test test/unit/std/string_spec.spl

# List available tests
docker run --rm -v $(pwd):/workspace:ro \
  simple-test-isolation:latest test --list
```

---

## Local Development Workflow

### Daily Cycle

1. **Edit code:** `vim src/lib/text.spl`
2. **Quick local test:** `bin/simple test test/unit/std/string_spec.spl`
3. **Verify in container:** `scripts/local-container-test.sh quick test/unit/std/string_spec.spl`
4. **Commit:** `jj commit -m "fix: String.trim edge case"`

### Run by Test Tier

```bash
# Unit tests (fast tier)
docker run --rm -v $(pwd):/workspace:ro \
  --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test test/unit/

# Integration tests (standard tier)
docker run --rm -v $(pwd):/workspace:ro \
  --memory=1g --cpus=2.0 \
  simple-test-isolation:latest test test/integration/

# System tests (slow tier)
docker run --rm -v $(pwd):/workspace:ro \
  --memory=2g --cpus=4.0 \
  simple-test-isolation:latest test test/system/
```

---

## Resource Profiles

Tests are categorized into resource tiers. Configure in `simple.test.sdn`:

| Profile | Memory | CPU | Timeout | Use For |
|---------|--------|-----|---------|---------|
| **Fast** | 128MB | 0.5 | 30s | Unit tests -- pure logic |
| **Standard** | 512MB | 1.0 | 2min | Integration -- module tests |
| **Slow** | 1GB | 2.0 | 10min | System -- full compilation |
| **Intensive** | 2GB | 4.0 | 30min | Self-hosting, heavy builds |
| **Critical** | 4GB | 8.0 | 1hr | QEMU, baremetal, cross-platform |

### Tagging Tests with Profiles

```simple
# Fast (default -- no tag needed)
describe "String.trim":
    it "removes whitespace":
        expect("  hello".trim()).to_equal("hello")

# Slow
describe "File compilation":
    slow_it "compiles large file":
        val result = compile("examples/large_app.spl")
        expect(result.?).to_equal(true)

# Critical
describe "QEMU testing":
    critical_it "boots on RISC-V baremetal":
        val result = run_qemu_riscv("bin/kernel.elf")
        expect(result.exit_code).to_equal(0)
```

### CLI Override

```bash
# Force specific profile
docker run --rm -v $(pwd):/workspace:ro \
  --memory=1g --cpus=2.0 \
  simple-test-isolation:latest test --profile=slow

# Run only tests of a specific tier
bin/simple test --only-fast
bin/simple test --only-slow
```

### Configuration File

```sdn
test:
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

  default_profile: fast
```

---

## Container Runtime Options

### Docker vs Podman

| Feature | Docker | Podman |
|---------|--------|--------|
| Daemon required | Yes | No |
| Root required | Typically | No (rootless) |
| Windows/macOS support | Better | Requires VM |
| Security model | Standard | Better on Linux |

Both work identically for Simple tests:

```bash
bin/simple test --container --container-runtime=docker
bin/simple test --container --container-runtime=podman
bin/simple test --container --container-runtime=auto   # auto-detect
```

---

## Helper Scripts

### local-container-test.sh

Developer-friendly wrapper:

```bash
scripts/local-container-test.sh quick test/unit/std/string_spec.spl  # Single test
scripts/local-container-test.sh unit           # Unit tests
scripts/local-container-test.sh integration    # Integration tests
scripts/local-container-test.sh system         # System tests
scripts/local-container-test.sh all            # All test suites
scripts/local-container-test.sh shell          # Interactive debugging
scripts/local-container-test.sh build          # Rebuild container
scripts/local-container-test.sh status         # Health check
```

### ci-test.sh

CI runner helper:

```bash
scripts/ci-test.sh                                    # All tests, fast profile
TEST_PROFILE=standard scripts/ci-test.sh test/unit/   # Unit tests, standard profile
CONTAINER_RUNTIME=podman scripts/ci-test.sh           # Use Podman
```

Environment variables: `CONTAINER_IMAGE`, `CONTAINER_RUNTIME`, `TEST_PROFILE`, `OUTPUT_FORMAT`.

---

## Docker Compose

```bash
docker-compose up unit-tests        # Fast unit tests (128MB, 0.5 CPU)
docker-compose up integration-tests # Standard (512MB, 1.0 CPU)
docker-compose up system-tests      # Slow (1GB, 2.0 CPU)
docker-compose up all-tests         # Parallel (2GB, 4.0 CPU)
docker-compose run dev-shell        # Interactive shell (read-write)
docker-compose up watch-tests       # Auto-run on file changes
docker-compose down                 # Clean up
```

---

## Security Hardening

Containers run with minimal privileges by default:

```bash
docker run --rm \
  -v $(pwd):/workspace:ro \         # Read-only workspace
  --read-only \                      # Read-only root filesystem
  --tmpfs /tmp:rw,noexec,nosuid \    # Writable /tmp, no executables
  --cap-drop=ALL \                   # Drop all capabilities
  --security-opt=no-new-privileges \ # Prevent privilege escalation
  --user=1001:1001 \                 # Non-root user
  simple-test-isolation:latest test
```

Add specific capabilities only when needed:

```bash
# Network tests requiring raw sockets
docker run --rm -v $(pwd):/workspace:ro \
  --cap-add=NET_RAW \
  simple-test-isolation:latest test test/network/
```

---

## Platform Considerations

### macOS

Docker Desktop uses a VM, adding ~10-20% overhead. Adjust limits accordingly:

```bash
docker run --rm -v $(pwd):/workspace:ro \
  --memory=640m --cpus=1.2 \
  simple-test-isolation:latest test
```

### Windows

```bash
# PowerShell
docker run --rm -v ${PWD}:/workspace:ro --memory=512m --cpus=1.0 simple-test-isolation:latest test

# CMD
docker run --rm -v %cd%:/workspace:ro --memory=512m --cpus=1.0 simple-test-isolation:latest test
```

Configure Docker Desktop: Settings -> Resources -> Memory: 4GB minimum, CPUs: 4 cores minimum.

### Resource Monitoring

```bash
# Real-time stats (separate terminal)
docker stats simple-test

# Post-execution analysis
docker inspect simple-test | jq '.[0].HostConfig.Memory'
```

---

## Troubleshooting

| Problem | Solution |
|---------|----------|
| Container not found | `docker build -t simple-test-isolation:latest -f docker/Dockerfile.test-isolation .` |
| Permission denied | `chmod -R a+rX .` or run with `--user=$(id -u):$(id -g)` |
| Out of memory (exit code 137) | Increase `--memory` or tag test as `slow_it` / `intensive_it` |
| Timeout | Use `--profile=slow` or `--timeout=600` |
| Volume mount (Windows) | PowerShell: `${PWD}`, CMD: `%cd%` |
| Tests pass locally, fail CI | Run exact CI command: `scripts/ci-test.sh test/unit/` |
| Docker not running | `sudo systemctl start docker` or start Docker Desktop |
| Build fails "no such file" | Verify you are in project root and `bin/simple` or `bin/release/<platform>/simple` exists |

### Interactive Debugging

```bash
docker run -it --rm -v $(pwd):/workspace \
  --entrypoint /bin/bash \
  simple-test-isolation:latest

# Inside container:
simple test test/unit/failing_spec.spl --verbose
```

### Parallel Execution

```bash
for i in {1..4}; do
  docker run --rm -v $(pwd):/workspace:ro \
    --memory=512m --cpus=1.0 \
    --name simple-test-$i \
    simple-test-isolation:latest test --parallel --shard=$i/4 &
done
wait
```

### Best Practices

1. **Start with fast profile** -- default all tests to fast, only promote when necessary
2. **Measure before promoting** -- use `--verbose` to see actual resource usage
3. **Isolate slow operations** -- extract slow parts into separate test files
4. **Use mocks for I/O** -- mock file/network operations in unit tests
5. **Clean up resources** -- close files, connections in `after_each` hooks
6. **Document assumptions** -- note why a test needs intensive/critical profile
