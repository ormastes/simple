# T32 Hardware Integration Testing Guide

## 1. Prerequisites

- **TRACE32 PowerView** installed (typically `/opt/t32/`) with RCL/NETTCP enabled
- **Hardware probe** (Lauterbach PowerTrace/PowerDebug) connected via USB
- **Target board** (e.g., STM32WB, STM32H7) powered and wired to the probe
- **Network**: PowerView must be reachable on its RCL port (default 20000)
- **`bin/simple`**: run `scripts/setup.sh` to create the symlink

## 2. Environment Setup

```bash
# Required
export T32_HW_HOST=localhost        # PowerView host (or remote IP)
export T32_HW_PORT=20000            # RCL port configured in config.t32

# Optional — paths auto-detected if on PATH or in /opt/t32/
export T32REM=/opt/t32/bin/pc_linux64/t32rem
export T32_API_LIB=/opt/t32/bin/pc_linux64/t32api64.so
export T32_RCL_PROTOCOL=NETTCP      # NETTCP (default) or UDP
```

Verify connectivity before running tests:

```bash
scripts/t32_check_ready.shs localhost 20000
```

## 3. Backend Configuration

The test suite supports three T32 communication backends:

| Backend | Env / Detection | Best For |
|---------|----------------|----------|
| **t32rem** | `T32REM` path or on `PATH` | CLI scripting, simple commands |
| **ctypes** | `T32_API_LIB` pointing to `t32api64.so` | Low-latency, full API access |
| **python_rcl** | `python3 -c "import lauterbach.trace32"` | Python-based workflows |

Set `T32_BACKEND_PREFERENCE` to force a specific backend; leave empty for auto-detection (tries t32rem, ctypes, python_rcl in order).

## 4. Running Tests

```bash
# Full suite — all numbered specs + MCP e2e
scripts/t32_run_hw_tests.shs

# Quick smoke — preflight + open/close + cmd_run + eval
scripts/t32_run_hw_tests.shs --quick

# Preflight only — verify environment without touching hardware
scripts/t32_run_hw_tests.shs --preflight-only

# Single backend validation
scripts/t32_run_hw_tests.shs --backend ctypes
scripts/t32_run_hw_tests.shs --backend t32rem
scripts/t32_run_hw_tests.shs --backend python_rcl

# Individual spec file
bin/simple test test/integration/t32_hw/13_cmd_run_spec.spl
```

## 5. Adding New Tests

Test files live in `test/integration/t32_hw/` with numbered prefixes for ordering:

```
00_preflight_spec.spl          # Always runs first
01-09  lifecycle (power, open/close)
10-19  core operations (session, cmd, eval)
20-29  advanced features (fields, actions, screenshots)
30-39  dialogs, jobs
40-49  window management
50     session close (always last)
```

Use helpers from `t32_hw_helpers.spl`:

```simple
use test.integration.t32_hw.t32_hw_helpers.{t32_hw_host, t32_hw_port, t32_hw_skip_unless_reachable}

describe "my new feature":
    before_each:
        t32_hw_skip_unless_reachable()

    it "does something":
        # test body
```

Backend-specific tests go in `test/integration/t32_hw/backends/<name>_spec.spl`.

## 6. CI/CD Integration

The `docker-compose.test.yml` config provides an isolated environment:

```bash
# Run hw tests in container (requires USB passthrough for probe)
docker compose -f config/docker-compose.test.yml run --rm t32-hw-test

# Or use the local container script
scripts/local-container-test.sh t32-hw
```

Key CI considerations:
- Tests exit 2 for SKIP (no hardware), 1 for FAIL, 0 for PASS
- `--preflight-only` can gate expensive test stages
- Set `T32_HW_HOST` to the Docker host IP when the probe is on the host

## 7. Troubleshooting

| Symptom | Cause | Fix |
|---------|-------|-----|
| `Cannot connect to host:port` | PowerView not running or RCL disabled | Start PowerView; check `RCL=NETTCP` in `config.t32` |
| `t32rem PING failed` | Wrong protocol or firewall | Try `T32_RCL_PROTOCOL=UDP`; check `ss -ltnup \| grep 20000` |
| `No T32 backends found` | Missing t32rem, API lib, and python module | Install at least one; set `T32REM` or `T32_API_LIB` |
| `probe is already claimed` | Another PowerView session holds the probe | `scripts/t32_check_ready.shs --kill-stale` |
| `Device or resource busy` | USB permissions | `scripts/t32_check_ready.shs --repair-devlink` |
| Timeout on long operations | Default 5s command timeout too short | Set `T32_CMD_TIMEOUT_MS=15000` |
| Preflight passes, tests skip | `t32_hw_skip_unless_reachable()` guard | Verify host/port env vars match running PowerView |
