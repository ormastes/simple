# T32 MCP Real Hardware Test Execution Plan

**Date:** 2026-04-02
**Status:** Pending — requires T32 hardware environment
**Depends on:** doc/03_plan/t32_mcp_hw_integration_tests.md (spec scaffolding)

## Problem

Test specs exist in `test/integration/t32_hw/` (32 files, 141 assertions) but have
ONLY been verified in interpreter mode which checks file loading, NOT `it` block
execution. Zero tests have run against real T32 hardware. Zero backend interfaces
(RCL, Python, C API) have been validated.

## Prerequisites

### Hardware
- Lauterbach TRACE32 PowerView installed (`/opt/t32` or custom path)
- Debug probe connected (PowerDebug, CombiProbe, or µTrace)
- Target board powered and connected (ARM Cortex-M preferred for initial validation)
- USB relay for power control (optional, needed for power cycle tests)

### Software
- `t32rem` binary accessible (`T32_PATH/bin/pc_linux64/t32rem`)
- T32 PowerView running with RCL enabled: `RCL=NETTCP PORT=20000`
- Python 3 + `pip install lauterbach.trace32.rcl` (for Python backend)
- `t32api64.so` at `T32_PATH/bin/pc_linux64/t32api64.so` (for C API backend)
- Simple compiler built: `bin/simple` or `bin/release/<platform>/simple` available

### Environment Variables
```bash
export T32_PATH=/opt/t32
export T32_HW_HOST=localhost
export T32_HW_PORT=20000
# Optional:
export T32_BACKEND_PREFERENCE=t32rem   # or python_rcl or ctypes
export T32_PYTHON_BINARY=python3
export T32_API_LIB_PATH=/opt/t32/bin/pc_linux64/t32api64.so
export RELAY_DEVICE=/dev/ttyACM0       # for power relay
```

## Execution Steps

### Step 1: Verify T32 is running and reachable

```bash
# Check t32rem can connect
$T32_PATH/bin/pc_linux64/t32rem localhost port=20000 PING

# Check version
$T32_PATH/bin/pc_linux64/t32rem localhost port=20000 VERSION.BUILD()
```

Expected: PING returns ok, VERSION.BUILD() returns numeric build number.

### Step 2: Run pre-flight test (interpreter mode — structure check)

```bash
bin/simple test test/integration/t32_hw/00_preflight_spec.spl
```

Expected: File loads, assertions counted. Bodies don't execute.

### Step 3: Run pre-flight in compiled mode (REAL execution)

```bash
bin/simple test --mode=native test/integration/t32_hw/00_preflight_spec.spl
```

Expected: `it` blocks actually execute. Tests should:
- Detect t32rem binary
- TCP connect to T32 port
- Query VERSION.BUILD() and get a real number
- Check relay scripts if relay hardware is present

**If this step fails**, fix the connection/path issues before proceeding.

### Step 4: Run Phase 0 isolated tests (compiled mode)

```bash
bin/simple test --mode=native test/integration/t32_hw/00_preflight_spec.spl
bin/simple test --mode=native test/integration/t32_hw/01_power_cycle_spec.spl
bin/simple test --mode=native test/integration/t32_hw/02_t32_open_close_spec.spl
```

Record results for each file. Power cycle test requires relay hardware.

### Step 5: Run Phase 1 OLD tool tests (compiled mode)

```bash
for f in test/integration/t32_hw/1*_spec.spl; do
  echo "=== $f ==="
  bin/simple test --mode=native "$f"
done
```

These share a T32 session. Run in numeric order (10, 11, 12, ..., 19).
Expected: All 19 OLD tools respond correctly via t32rem.

### Step 6: Run Phase 2 NEW tool tests (compiled mode)

```bash
for f in test/integration/t32_hw/2*_spec.spl; do
  echo "=== $f ==="
  bin/simple test --mode=native "$f"
done
```

Includes power cycle at start (20), then NEW tools (21-29).

### Step 7: Run Phase 3 dialog + Phase 4 window + Phase 5 teardown

```bash
bin/simple test --mode=native test/integration/t32_hw/30_dialog_tools_spec.spl
bin/simple test --mode=native test/integration/t32_hw/40_window_reopen_spec.spl
bin/simple test --mode=native test/integration/t32_hw/50_session_close_spec.spl
```

### Step 8: Run t32rem backend (explicit)

```bash
T32_BACKEND_PREFERENCE=t32rem \
  bin/simple test --mode=native test/integration/t32_hw/backends/t32rem_spec.spl
```

### Step 9: Run Python RCL backend

```bash
# First verify Python package
python3 -c "import lauterbach.trace32.rcl; print('OK')"

T32_BACKEND_PREFERENCE=python_rcl \
  bin/simple test --mode=native test/integration/t32_hw/backends/python_rcl_spec.spl
```

### Step 10: Run C API / ctypes backend

```bash
# Verify library exists
ls -la $T32_PATH/bin/pc_linux64/t32api64.so

T32_BACKEND_PREFERENCE=ctypes \
  bin/simple test --mode=native test/integration/t32_hw/backends/ctypes_spec.spl
```

**Must be compiled mode** — ctypes requires `spl_dlopen`.

### Step 11: Run config file backend

```bash
bin/simple test --mode=native test/integration/t32_hw/backends/config_file_spec.spl
```

### Step 12: Run full suite (compiled mode)

```bash
bin/simple test --mode=native test/integration/t32_hw/
```

### Step 13: Compiled SMF mode validation

```bash
bin/simple test --mode=smf test/integration/t32_hw/modes/compiled_smf_spec.spl
```

## Result Recording

After each step, record in `doc/08_tracking/test/t32_hw_test_results.md`:

```markdown
| Step | File(s) | Mode | Backend | Passed | Failed | Notes |
|------|---------|------|---------|--------|--------|-------|
| 3 | 00_preflight | native | t32rem | ? | ? | |
| 4 | 01_power_cycle | native | t32rem | ? | ? | |
| ... | | | | | | |
```

## Expected Failures and Workarounds

| Test | Likely Issue | Fix |
|------|-------------|-----|
| 01_power_cycle | No relay hardware | Skip; set `RELAY_DEVICE` if available |
| 23_screenshot | Headless mode, no display | Uses `pass_todo`; needs Xvfb or visible GUI |
| 30_dialog | No CMM dialog script on host | `DIALOG.Message` may not work on all configs |
| ctypes backend | t32api64.so missing | Install T32 SDK or skip |
| python_rcl backend | Package not installed | `pip install lauterbach.trace32.rcl` |

## Success Criteria

- [ ] Pre-flight (00): all 5 assertions pass in compiled mode
- [ ] Session open/close (02): connect + disconnect + reconnect works
- [ ] All 19 OLD tools: respond without error via t32rem
- [ ] All 17 NEW tools: respond without error via t32rem
- [ ] t32rem backend: 7 shared tests pass
- [ ] Python RCL backend: 7 shared tests pass (if package installed)
- [ ] C API backend: 7 shared tests pass in compiled mode (if library available)
- [ ] Window reopen: capture works after WinCLEAR + reopen
- [ ] Session close: clean disconnect, no orphan processes
- [ ] Full suite in compiled mode: 0 unexpected failures

## After Validation

1. Update `doc/01_research/local/t32_mcp_hw_integration_tests.md` status to "Validated"
2. Update `doc/03_plan/t32_mcp_hw_integration_tests.md` status to "Complete"
3. Write results to `doc/08_tracking/test/t32_hw_test_results.md`
4. Fix any test specs that fail due to wrong T32 command syntax
5. Commit and push results
