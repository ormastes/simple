# T32 Hardware Test Results

**Date:** 2026-04-02
**T32 Version:** R.2013.02.000045901 (Build 42354, Jul 24 2013)
**Probe:** Lauterbach Power Debug II (USB, ID 0897:0002)
**CPU:** ARMV8
**Host:** Linux x86_64, Xvfb :99
**Connection:** C API via UDP, port 20000 (RCL=NETASSIST)

## Config Bugs Found and Fixed

| Bug | File | Fix |
|-----|------|-----|
| `SYS=/opt/t32/bin/pc_linux64` (wrong) | config/t32_stm_linux_hidden.t32 | Changed to `SYS=/opt/t32` |
| `RCL=` + `NETTCP` split across lines | config/t32_stm_linux_hidden.t32 | Changed to `RCL=NETASSIST` on one line |
| T32 fonts not in X font path | Xvfb startup | Must start Xvfb with `-fp /tmp/t32fonts/` after mkfontdir |
| "TRACE32 device already in use" dialog | Stale USB lock | Kill old T32 and remove lock files before restart |

## Command Test Results (via C API)

### Working Commands

| Command | Output | Notes |
|---------|--------|-------|
| `PRINT VERSION.BUILD()` | 45901 | Build number |
| `PRINT VERSION.SOFTWARE()` | R.2013.02.000045901 | Full version string |
| `PRINT VERSION.DATE()` | 2013/02 | Release date |
| `PRINT CPU()` | ARMV8 | Target architecture |
| `PRINT STATE.RUN()` | FALSE | Target not running |
| `PRINT SYStem.Mode()` | 0 | System down |
| `PRINT DEBUGMODE()` | MIX | Debug mode |
| `SYStem.Up` | executed | Powers up target |
| `SYStem.Down` | executed | Powers down target |
| `SYStem.RESetTarget` | "target reset" | Hardware reset |
| `Register` | executed | Opens register window |
| `Step` | executed | Single instruction step |
| `Break` | "emulation not running" | Expected when target stopped |
| `PRINT "hello"` | hello | PRINT works |

### Failing Commands (Not Available in 2013 Build)

| Command | Error | Notes |
|---------|-------|-------|
| `PRINT PRACTICE.STATE()` | erroneous command | Added in later versions |
| `AREA.Create T32_HW_TEST` | erroneous command | AREA management changed |
| `AREA.Select T32_HW_TEST` | erroneous command | AREA management changed |
| `PRINT VERSION.ENvironment()` | erroneous command | Not in this build |

## Backend Test Results

| Backend | Status | Notes |
|---------|--------|-------|
| C API (UDP) | **WORKS** | Compiled from /opt/t32/demo/api/capi/, connects via UDP 20000 |
| t32rem CLI | **BROKEN** | "error initializing TRACE32" — binary can't initialize its own API |
| Python RCL | **INCOMPATIBLE** | lauterbach.trace32.rcl 1.1.5 requires SOFTWARE.BUILD() which doesn't exist in 2013 build |
| ctypes | **NO LIBRARY** | t32api64.so not found in this installation |

## Test Spec Impact

Tests that need updating for 2013 build compatibility:

| Spec File | Issue | Fix Needed |
|-----------|-------|------------|
| 15_eval_spec.spl | Tests PRACTICE.STATE() | Remove or gate on version |
| 14_cmm_run_spec.spl | Uses AREA.Create/Select | Use alternative commands |
| 19_resources_spec.spl | Tests VERSION.ENvironment() | Use VERSION.DATE() instead |
| 24_history_tail_spec.spl | Uses PRACTICE.STATE() | Remove or gate |
| 25_status_snapshot_spec.spl | Uses PRACTICE.STATE() | Use STATE.RUN() only |
| 27_area_read_spec.spl | Uses AREA.Create/Select | Needs newer T32 |
| 28_setup_headless_spec.spl | Uses AREA operations | Needs newer T32 |
| 30_dialog_tools_spec.spl | Uses DIALOG commands | Needs newer T32 |
| backends/python_rcl_spec.spl | Python API incompatible | Skip on 2013 build |

## Next Steps

1. Update test specs to gate commands by T32 version (>= 45901 = 2013, >= newer = AREA/PRACTICE)
2. Fix t32rem binary issue (may need rebuilding or newer version)
3. Build tests around the C API as primary backend
4. Consider upgrading T32 installation for full command coverage
