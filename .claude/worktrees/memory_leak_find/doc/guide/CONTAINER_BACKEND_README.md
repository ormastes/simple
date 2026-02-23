# Container Backend for Test Runner

**Implementation Date:** 2026-02-14
**Status:** Complete - Phase 2 of Robust Test Runner Plan

---

## Quick Start

### 1. Build Container Image

```bash
./scripts/docker-build-test-runner.sh
```

### 2. Run Tests in Container

```bash
# Enable container mode
bin/simple test --container

# Or specify mode
bin/simple test --mode=container

# Single test file
bin/simple test test/unit/std/string_spec.spl --container
```

---

## What Was Implemented

### ✅ Phase 2: Container Integration (Complete)

1. **Container Backend Module** (`src/app/test_runner_new/test_runner_container.spl`)
   - Docker/Podman detection
   - Container execution
   - Image verification
   - Volume cleanup

2. **Execution Integration** (`test_runner_execute.spl`)
   - `run_test_file_container()` function
   - Resource limits (512MB RAM, 1.0 CPU)
   - Network isolation
   - Read-only workspace

3. **Configuration Support** (`test_config.spl`)
   - `container_enabled: bool`
   - `container_runtime: text` (auto/docker/podman)
   - `container_image: text`

4. **CLI Flags** (`test_runner_args.spl`)
   - `--container`
   - `--container-runtime=X`
   - `--container-image=X`
   - `--mode=container`

5. **Docker Support**
   - Dockerfile (`docker/test-runner.Dockerfile`)
   - Build script (`scripts/docker-build-test-runner.sh`)
   - Alpine-based image (~50-100MB)
   - Non-root user execution

6. **Tests & Documentation**
   - Unit tests (`test/unit/app/test_runner_new/container_backend_spec.spl`)
   - User guide (`doc/guide/test_runner_container.md`)
   - Example config (`docker/simple.test.container.sdn`)

---

## Files Created

```
src/app/test_runner_new/
  test_runner_container.spl         # 158 lines - Core backend

docker/
  test-runner.Dockerfile            # Container image definition

scripts/
  docker-build-test-runner.sh       # Build automation script

test/unit/app/test_runner_new/
  container_backend_spec.spl        # Unit tests

doc/guide/
  test_runner_container.md          # Complete guide

doc/test/
  container_implementation_verification.md  # Verification report

docker/simple.test.container.sdn   # Configuration example
```

## Files Modified

```
src/app/test_runner_new/
  test_config.spl         # +15 lines - Config fields
  test_runner_types.spl   # +4 lines - Container mode enum
  test_runner_args.spl    # +35 lines - CLI flags
  test_runner_execute.spl # +71 lines - Container execution
  test_runner_main.spl    # +8 lines - Mode integration
```

**Total**: 291 lines added/modified

---

## CLI Reference

### Flags

| Flag | Description | Default |
|------|-------------|---------|
| `--container` | Enable container execution | `false` |
| `--container-runtime=X` | Runtime: `auto`, `docker`, `podman` | `auto` |
| `--container-image=X` | Image name | `simple-test-runner:latest` |
| `--mode=container` | Set execution mode to container | - |

### Examples

```bash
# Basic container execution
bin/simple test --container

# Specify Docker explicitly
bin/simple test --container-runtime=docker

# Use custom image
bin/simple test --container-image=my-test-image:v1.0

# Container mode with verbose output
bin/simple test --mode=container --verbose

# Run specific test file
bin/simple test test/unit/std/string_spec.spl --container
```

---

## Configuration File

Add to `simple.test.sdn`:

```sdn
# Container execution settings
container_enabled: true
container_runtime: auto
container_image: simple-test-runner:latest
```

---

## Container Specifications

### Resource Limits
- **Memory**: 512 MB (enforced by Docker)
- **CPU**: 1.0 CPUs
- **Network**: None (isolated)
- **Filesystem**: Read-only workspace mount

### Image Details
- **Base**: Alpine Linux 3.19
- **User**: testuser (UID 1000, non-root)
- **Entrypoint**: `/usr/local/bin/simple`
- **Working Dir**: `/workspace`
- **Size**: ~50-100 MB

---

## Performance

| Mode | Overhead | Isolation | Use Case |
|------|----------|-----------|----------|
| Native | 0ms | None | Fast iteration |
| Process | 5-10ms | Process | Standard testing |
| Safe Mode | 10-20ms | ulimit | Slow tests |
| **Container** | **50-100ms** | **Full** | **Critical tests** |

**Recommendation**: Use container mode for critical tests requiring full isolation.

---

## Troubleshooting

### "No container runtime found"
Install Docker or Podman:
```bash
# Ubuntu/Debian
sudo apt-get install docker.io

# macOS
brew install docker
```

### "Container image not found"
Build the image:
```bash
./scripts/docker-build-test-runner.sh
```

### "Permission denied"
Add user to docker group:
```bash
sudo usermod -aG docker $USER
newgrp docker
```

---

## Documentation

- **User Guide**: `doc/guide/test_runner_container.md`
- **Implementation Plan**: `doc/research/robust_test_runner_plan_2026-02-14.md`
- **Verification Report**: `doc/test/container_implementation_verification.md`
- **Example Config**: `docker/simple.test.container.sdn`

---

## Future Enhancements

Planned for upcoming phases:

1. **Resource Profiles** (Phase 1.2)
   - Fast/Standard/Slow/Intensive profiles
   - Auto-detection from test markers

2. **Resource Monitoring** (Phase 3.1)
   - CPU/Memory tracking
   - Violation detection
   - Usage reports

3. **Per-Test Containers** (Phase 4.1)
   - Individual container per test
   - Filesystem snapshots
   - Auto-cleanup

4. **Distributed Execution** (Phase 5.1)
   - Worker pools
   - Task distribution
   - CI/CD integration

---

## Support

For issues:
1. Check `doc/guide/test_runner_container.md`
2. Verify runtime: `docker --version`
3. Check image: `docker images simple-test-runner`
4. Run with `--verbose` for detailed output

---

## Summary

✅ **Complete Implementation** of container backend for test runner
- Docker and Podman support
- Full test isolation
- Resource limits
- Network isolation
- Non-root execution
- Production-ready

🎯 **Ready for Use** - All Phase 2 requirements met
