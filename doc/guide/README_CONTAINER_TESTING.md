# Container Testing Documentation Index

This directory contains comprehensive documentation for container-based testing in the Simple language compiler project.

## Quick Start

**For developers:**
1. Read `container_testing.md` (10 min read)
2. Run `scripts/local-container-test.sh unit` to try it out
3. Use `docker-compose up unit-tests` for daily development

**For CI/CD engineers:**
1. Read `resource_limits.md` (resource profiles)
2. Review `.github/workflows/containerized-tests.yml`
3. Use `scripts/ci-test.sh` in your pipeline

---

## Documentation Files

### Core Guides

#### 1. **container_testing.md** (Primary Guide)
**Full guide to container-based testing**

Topics covered:
- Overview and benefits (isolation, reproducibility, resource control)
- Quick start (prerequisites, build, run)
- Local development workflow (edit → test → verify)
- Resource profile configuration (fast/standard/slow/intensive/critical)
- Container runtime options (Docker vs Podman)
- Security hardening (capabilities, read-only filesystem)
- Troubleshooting (15+ common issues with solutions)
- Advanced usage (parallel execution, custom environments, debugging)

**Use this when:**
- Setting up container testing for the first time
- Debugging container-related issues
- Learning best practices for isolated testing
- Configuring CI/CD pipelines

**Key sections:**
- Quick Start (lines 11-60)
- Local Development Workflow (lines 62-110)
- Troubleshooting (lines 190-280)

---

#### 2. **resource_limits.md** (Resource Management)
**Understanding and configuring resource limits for tests**

Topics covered:
- Resource profile tiers (Fast, Standard, Slow, Intensive, Critical)
- Detailed limits for each tier (memory, CPU, timeout, I/O)
- Per-test tagging (`slow_it`, `intensive_it`, `critical_it`)
- Global configuration in `simple.test.sdn`
- CLI overrides (`--profile=slow`, `--only-fast`, etc.)
- Platform-specific considerations (Linux, macOS, Windows, FreeBSD)
- Resource limit enforcement (memory, CPU, I/O)
- Monitoring resource usage (during and post-execution)
- Troubleshooting resource issues
- Best practices (start fast, measure, isolate, mock)

**Use this when:**
- Tests timeout or run out of memory
- Configuring new test profiles
- Optimizing CI/CD resource allocation
- Understanding why a test needs specific limits
- Debugging platform-specific issues

**Key sections:**
- Profile Tiers (lines 13-150)
- Platform Considerations (lines 190-270)
- Troubleshooting (lines 330-400)

---

### CI/CD Integration

#### 3. **.github/workflows/containerized-tests.yml**
**GitHub Actions workflow for containerized testing**

Features:
- Build test container with cache
- Matrix strategy: Unit/Integration/System × Docker/Podman
- Parallel execution (4 shards)
- Resource limit verification
- JSON test result parsing
- Combined result reporting

**Jobs:**
- `build-container` - Build and cache test image
- `unit-tests-docker` / `unit-tests-podman` - Fast unit tests
- `integration-tests-docker` / `integration-tests-podman` - Standard integration tests
- `system-tests-docker` - Slow system tests
- `parallel-tests` - 4-way parallel execution
- `resource-limits` - Verify memory/CPU enforcement
- `summary` - Aggregate results and check for failures

**Triggers:**
- Push to main/master/develop
- Pull requests
- Daily at 02:00 UTC (scheduled)
- Manual (workflow_dispatch)

---

#### 4. **.github/workflows/test-isolation.yml**
**Critical test isolation workflow (QEMU, baremetal, cross-platform)**

Features:
- Gated execution (main branch, labels, schedule, manual)
- QEMU VM tests (RISC-V, ARM64)
- Baremetal boot tests
- Cross-platform builds (7 targets)
- Compiler self-hosting (intensive)
- Memory stress tests (4GB limit)

**Jobs:**
- `check-trigger` - Gate: only run on main, labels, schedule
- `build-isolation-container` - Build test container
- `qemu-tests` - RISC-V and ARM64 QEMU tests
- `baremetal-tests` - Baremetal boot verification
- `cross-platform-builds` - Linux/Windows/Darwin/FreeBSD targets
- `self-hosting` - Compiler self-hosting build
- `memory-stress` - 4GB memory stress tests
- `summary` - Aggregate critical test results (not blocking)

**Triggers:**
- Push to main (always)
- PR with `test:critical` label
- Weekly on Sundays at 03:00 UTC
- Manual with profile selection

**Note:** Critical tests are NOT required for PR merge. They verify advanced functionality.

---

### Helper Scripts

#### 5. **script/ci-test.sh**
**CI test runner helper (bash)**

Usage: `scripts/ci-test.sh [TEST_PATH]`

Features:
- Auto-detect container runtime (podman → docker)
- Build container if missing
- Run tests with resource profile
- Parse JSON results (if jq installed)
- Color-coded output
- Resource limit enforcement

Environment variables:
- `CONTAINER_IMAGE` - Image name (default: simple-test-isolation:latest)
- `CONTAINER_RUNTIME` - Runtime: auto|docker|podman (default: auto)
- `TEST_PROFILE` - Profile: fast|standard|slow|intensive|critical (default: fast)
- `OUTPUT_FORMAT` - Format: json|progress|doc (default: json)

Examples:
```bash
# All tests, fast profile
scripts/ci-test.sh

# Unit tests, standard profile
TEST_PROFILE=standard scripts/ci-test.sh test/unit/

# Slow tests with custom image
CONTAINER_IMAGE=simple-test:dev TEST_PROFILE=slow scripts/ci-test.sh test/system/

# Use Podman
CONTAINER_RUNTIME=podman scripts/ci-test.sh
```

---

#### 6. **script/local-container-test.sh**
**Developer-friendly container test wrapper (bash)**

Usage: `scripts/local-container-test.sh [COMMAND]`

Commands:
- `quick <file>` - Run single test file
- `unit` - Run unit tests (fast)
- `integration` - Run integration tests (standard)
- `system` - Run system tests (slow)
- `all` - Run all test suites
- `shell` - Interactive debugging shell
- `build` - Build/rebuild container
- `status` - Container health check

Examples:
```bash
# Single test
scripts/local-container-test.sh quick test/unit/std/string_spec.spl

# All unit tests
scripts/local-container-test.sh unit

# Debug in container
scripts/local-container-test.sh shell

# Rebuild after Dockerfile changes
scripts/local-container-test.sh build
```

---

### Configuration Files

#### 7. **docker-compose.yml**
**Docker Compose for local development**

Services:
- `unit-tests` - Fast unit tests (128MB, 0.5 CPU)
- `integration-tests` - Standard integration tests (512MB, 1.0 CPU)
- `system-tests` - Slow system tests (1GB, 2.0 CPU)
- `all-tests` - Parallel execution (2GB, 4.0 CPU)
- `dev-shell` - Interactive shell (read-write volume)
- `watch-tests` - Auto-run on file changes
- `critical-tests` - QEMU/baremetal (4GB, 8.0 CPU, privileged)

Usage:
```bash
# Run specific tier
docker-compose up unit-tests

# Interactive shell
docker-compose run dev-shell

# Rebuild
docker-compose build --no-cache

# Clean up
docker-compose down
```

---

#### 8. **simple.test.sdn**
**Test configuration (SDN format)**

Key sections:
- `test.resource_profiles` - Resource limits per tier
- `test.timeout` / `test.slow_timeout` - Default timeouts
- `test.parallel` / `test.max_threads` - Parallel execution
- `test.cpu_throttle` - Resource-aware throttling
- `coverage.*` - Coverage requirements
- `reports.*` - Test result output

Resource profiles:
```sdn
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

---

#### 9. **docker/Dockerfile.test-isolation**
**Minimal test container (40MB)**

Base: Alpine Linux 3.18 (~7MB)
Runtime: Simple binary (33MB)

Features:
- Non-root user (UID 1001)
- Minimal dependencies (bash, coreutils, ca-certificates)
- glibc compatibility (libstdc++)
- Health check (simple --version)
- Security hardening (capabilities dropped, read-only fs)

Build:
```bash
docker build -t simple-test-isolation:latest -f docker/Dockerfile.test-isolation .
```

---

## Common Workflows

### Daily Development

1. **Edit code:** `vim src/std/text.spl`
2. **Quick test:** `bin/simple test test/unit/std/string_spec.spl`
3. **Verify isolated:** `scripts/local-container-test.sh quick test/unit/std/string_spec.spl`
4. **Commit:** `jj commit -m "fix: String.trim edge case"`

### Before Pushing

```bash
# Run all unit tests in container (matches CI)
scripts/local-container-test.sh unit

# Or use docker-compose
docker-compose up unit-tests
```

### Debugging Failures

```bash
# Run failing test with verbose output
docker run --rm -v $(pwd):/workspace:ro \
  simple-test-isolation:latest test test/failing_spec.spl --verbose

# Interactive debugging
scripts/local-container-test.sh shell
# Inside: simple test test/failing_spec.spl --verbose
```

### CI/CD Integration

```yaml
# .github/workflows/custom.yml
- name: Run tests in container
  run: |
    scripts/ci-test.sh test/unit/
```

---

## Troubleshooting Quick Reference

| Problem | Solution |
|---------|----------|
| Container not found | `docker build -t simple-test-isolation:latest -f docker/Dockerfile.test-isolation .` |
| Permission denied | `chmod +x bin/release/simple` or add user to docker group |
| Out of memory | Increase `--memory=512m` to `--memory=1g` |
| Timeout | Use `--profile=slow` (10 min) or `--profile=intensive` (30 min) |
| Volume mount (Windows) | PowerShell: `${PWD}`, CMD: `%cd%` |
| jq not installed | `sudo apt install jq` (Ubuntu) or `brew install jq` (macOS) |
| Docker not running | `sudo systemctl start docker` (Linux) or start Docker Desktop |
| Tests pass locally, fail CI | Run exact CI command: `scripts/ci-test.sh test/unit/` |

---

## Resource Profile Quick Reference

| Profile | Memory | CPU | Timeout | Use For |
|---------|--------|-----|---------|---------|
| **Fast** | 128MB | 0.5 | 30s | Unit tests - pure logic |
| **Standard** | 512MB | 1.0 | 2min | Integration - module tests |
| **Slow** | 1GB | 2.0 | 10min | System - full compilation |
| **Intensive** | 2GB | 4.0 | 30min | Self-hosting, heavy builds |
| **Critical** | 4GB | 8.0 | 1hr | QEMU, baremetal, cross-platform |

---

## See Also

- **CLAUDE.md** - Main development guide (Quick Commands, Troubleshooting)
- **doc/guide/test.md** - General test policy and structure
- **doc/guide/comprehensive_testing.md** - Testing methodology
- **.github/workflows/** - All CI/CD workflows
- **simple.test.sdn** - Test configuration file

---

## Getting Help

1. Check troubleshooting sections in guides
2. Run `scripts/local-container-test.sh status` to verify setup
3. Try in interactive shell: `scripts/local-container-test.sh shell`
4. Review CI logs: `.github/workflows/containerized-tests.yml`
5. Ask in project chat with error output and test file

---

**Last Updated:** 2026-02-14
**Maintainer:** Simple Language Project
**License:** Same as project (MIT/Apache 2.0)
