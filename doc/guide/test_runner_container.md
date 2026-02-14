# Test Runner Container Backend Guide

**Date:** 2026-02-14
**Status:** Implementation Complete
**Version:** Phase 2 - Container Integration

---

## Overview

The Simple Language test runner now supports **container-based test execution** using Docker or Podman. This provides:

- **Full Isolation**: Tests run in separate containers with dedicated resources
- **Resource Limits**: Enforced memory and CPU limits via container runtime
- **Network Isolation**: Tests cannot access external network by default
- **Reproducibility**: Consistent execution environment across machines

---

## Quick Start

### 1. Build Container Image

```bash
# Build the test runner image
./script/docker-build-test-runner.sh

# Or manually with Docker
docker build -f docker/test-runner.Dockerfile -t simple-test-runner:latest .

# Or with Podman
podman build -f docker/test-runner.Dockerfile -t simple-test-runner:latest .
```

### 2. Run Tests in Container

```bash
# Using --container flag
bin/simple test --container

# Using --mode=container
bin/simple test --mode=container

# Specify container runtime
bin/simple test --container --container-runtime=docker
bin/simple test --container --container-runtime=podman

# Specify custom image
bin/simple test --container --container-image=my-test-image:v1.0
```

### 3. Run Single Test File

```bash
# Run specific test in container
bin/simple test test/unit/std/string_spec.spl --container

# With verbose output
bin/simple test test/unit/std/string_spec.spl --container --verbose
```

---

## CLI Flags

| Flag | Description | Default |
|------|-------------|---------|
| `--container` | Enable container execution | `false` |
| `--container-runtime=RUNTIME` | Container runtime (`auto`, `docker`, `podman`) | `auto` |
| `--container-image=IMAGE` | Container image name | `simple-test-runner:latest` |
| `--mode=container` | Set execution mode to container | N/A |

---

## Configuration File

Create or modify `simple.test.sdn`:

```sdn
# Enable container execution
container_enabled: true

# Container runtime: auto (detect), docker, or podman
container_runtime: auto

# Container image name
container_image: simple-test-runner:latest
```

See `simple.test.container.example.sdn` for complete example.

---

## Container Specifications

### Default Resource Limits

- **Memory**: 512 MB
- **CPU**: 1.0 CPUs
- **Network**: None (isolated)
- **Filesystem**: Read-only workspace mount

### Container Features

- **Base Image**: Alpine Linux 3.19 (minimal footprint)
- **User**: Non-root `testuser` (UID 1000, GID 1000)
- **Working Directory**: `/workspace` (mounted from host)
- **Entrypoint**: `/usr/local/bin/simple`
- **Default Command**: `test`

### Security

- **Non-root execution**: Tests run as `testuser`, not `root`
- **Read-only mounts**: Source code is mounted read-only
- **Network isolation**: No network access by default
- **Resource limits**: Memory and CPU enforced by container runtime

---

## Implementation Details

### File Structure

```
src/app/test_runner_new/
  test_runner_container.spl      # Container backend implementation
  test_runner_execute.spl         # Container execution mode
  test_runner_types.spl           # ExecutionMode.Container variant
  test_runner_args.spl            # CLI flag parsing
  test_config.spl                 # Configuration loading

docker/
  test-runner.Dockerfile          # Container image definition

script/
  docker-build-test-runner.sh     # Image build script

test/unit/app/test_runner_new/
  container_backend_spec.spl      # Container backend tests
```

### Key Functions

**Container Detection**:
```simple
fn container_detect_runtime() -> text:
    # Returns "docker", "podman", or "none"
```

**Container Execution**:
```simple
fn container_run_test(
    test_file: text,
    runtime: text,
    image: text,
    memory_mb: i64,
    cpu_count: f64,
    network: text,
    readonly: bool,
    workspace: text
) -> (text, text, i64, i64):
    # Returns (stdout, stderr, exit_code, duration_ms)
```

**Image Verification**:
```simple
fn container_check_image(image: text, runtime: text) -> bool:
    # Returns true if image exists locally
```

---

## Testing

### Run Container Backend Tests

```bash
# Test container detection and basic functions
bin/simple test test/unit/app/test_runner_new/container_backend_spec.spl

# Run all test runner tests
bin/simple test test/unit/app/test_runner_new/
```

### Test Scenarios

1. **Container Detection**: Verifies Docker/Podman availability
2. **Version Retrieval**: Gets container runtime version
3. **Image Checking**: Validates image existence
4. **Volume Cleanup**: Tests cleanup functionality

---

## Troubleshooting

### Error: "No container runtime found"

**Problem**: Neither Docker nor Podman is installed or not in PATH.

**Solution**:
```bash
# Install Docker
sudo apt-get install docker.io  # Ubuntu/Debian
brew install docker              # macOS

# Or install Podman
sudo apt-get install podman      # Ubuntu/Debian
brew install podman              # macOS
```

### Error: "Container image not found"

**Problem**: The test runner image hasn't been built.

**Solution**:
```bash
# Build the image
./script/docker-build-test-runner.sh

# Verify image exists
docker images simple-test-runner
```

### Error: "Permission denied"

**Problem**: Current user doesn't have permission to run Docker commands.

**Solution**:
```bash
# Add user to docker group (Linux)
sudo usermod -aG docker $USER
newgrp docker

# Or use sudo
sudo bin/simple test --container
```

### Slow Container Startup

**Problem**: Container takes long to start.

**Solution**:
- Use `--container-runtime=podman` (often faster than Docker)
- Pre-pull the base image: `docker pull alpine:3.19`
- Consider caching: Run tests once to warm up container cache

---

## Performance Comparison

| Mode | Overhead | Isolation | Resource Limits | Use Case |
|------|----------|-----------|-----------------|----------|
| **Native** | ~0ms | None | None | Fast iteration |
| **Process** | ~5-10ms | Process | ulimit | Standard testing |
| **Safe Mode** | ~10-20ms | Process | ulimit enforced | Slow tests |
| **Container** | ~50-100ms | Full | Docker enforced | Critical tests |

**Recommendation**:
- Unit tests: Native or Process mode
- Integration tests: Process or Safe mode
- Critical/QEMU/Baremetal tests: Container mode

---

## Advanced Usage

### Custom Container Image

Build custom image with additional tools:

```dockerfile
FROM simple-test-runner:latest

USER root
RUN apk add --no-cache qemu-system-x86_64

USER testuser
```

Build and use:
```bash
docker build -f custom.Dockerfile -t my-test-runner:latest .
bin/simple test --container --container-image=my-test-runner:latest
```

### Container Runtime Selection

Force specific runtime:
```bash
# Use Docker explicitly
bin/simple test --container-runtime=docker

# Use Podman explicitly
bin/simple test --container-runtime=podman
```

### Debugging Container Execution

Enable verbose mode:
```bash
bin/simple test --container --verbose
```

Output shows:
- Container runtime detected
- Image name and resource limits
- Execution time breakdown

---

## Future Enhancements

Planned for future phases:

1. **Per-Test Containers** (Phase 4.1)
   - Each test runs in separate container
   - Auto-cleanup after test completion
   - Filesystem snapshots

2. **Resource Profiles** (Phase 1.2)
   - Fast profile: 128MB, 0.5 CPU
   - Standard profile: 512MB, 1.0 CPU
   - Slow profile: 1GB, 2.0 CPU
   - Intensive profile: 4GB, 4.0 CPU

3. **Distributed Execution** (Phase 5.1)
   - Worker pool with N containers
   - Task queue and distribution
   - Result aggregation

4. **CI/CD Integration** (Phase 5.2)
   - GitHub Actions workflow
   - GitLab CI pipeline
   - Container image caching

See `doc/research/robust_test_runner_plan_2026-02-14.md` for complete roadmap.

---

## References

- **Plan Document**: `doc/research/robust_test_runner_plan_2026-02-14.md`
- **Dockerfile**: `docker/test-runner.Dockerfile`
- **Build Script**: `script/docker-build-test-runner.sh`
- **Example Config**: `simple.test.container.example.sdn`
- **Tests**: `test/unit/app/test_runner_new/container_backend_spec.spl`

---

## Support

For issues or questions:
1. Check this guide first
2. Review test output with `--verbose`
3. Verify container runtime: `docker --version` or `podman --version`
4. Check image exists: `docker images simple-test-runner`
5. Review logs in container: `docker logs <container-id>`
