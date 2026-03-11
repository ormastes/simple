# REPL + Jupyter Kernel Implementation Report

**Date:** 2026-03-11
**Status:** Complete
**Tests:** 41/41 passing (19 REPL + 22 Jupyter)

---

## Overview

Implemented a full interactive REPL and Jupyter notebook kernel for the Simple language. Both use temp-file accumulation + subprocess execution, avoiding compiler imports for fast startup.

---

## Components Implemented

### 1. Simple REPL (`src/app/repl/main.spl` — 249 lines)

**Architecture:** Module-level `var` state + subprocess evaluation via `bin/release/simple`.

**Features:**
- Interactive prompt with banner (`Simple Language REPL v0.2.0`)
- Commands: `:help`, `:quit`/`:q`/`:exit`, `:clear`, `:history`, `:show`, `:load <file>`
- Declaration detection: `val`, `var`, `fn`, `class`, `struct`, `enum`, `trait`, `use`, `extern`, `type`, `alias`
- Statement detection: `if`, `while`, `for`, `match`, `print`, assignments
- Expression auto-print: wraps in `fn __repl_expr_N()` wrapper
- Multi-line input: lines ending with `:` enter continuation mode, empty line submits
- Error recovery: failed evaluations rollback accumulated state
- EOF handling: Ctrl-D terminates cleanly

**Key design decisions:**
- No compiler imports (avoided 40s+ startup from full compiler tree load)
- Uses `input()`, `stdout_write()`, `stdout_flush()` (names the binary already knows)
- Text accumulation (`var REPL_ACCUMULATED: text`) instead of arrays (avoids `.len()`/`.push()` path call bug)
- Subprocess execution with `</dev/null` stdin redirect to prevent interference

**CLI wiring:** `src/app/io/cli_commands.spl:37` — `cli_run_file("src/app/repl/main.spl", [], ...)`

### 2. Jupyter Kernel (`src/app/jupyter_kernel/main.spl` — 288 lines)

**Architecture:** JSON-lines protocol over stdin/stdout, bridged to Jupyter ZMQ wire protocol by Python wrapper.

**Protocol support:**
- `kernel_info_request` → language info, protocol version 5.4
- `execute_request` → evaluate code, send status/stream/error on iopub
- `is_complete_request` → heuristic (lines ending `:` = incomplete)
- `shutdown_request` → clean exit
- `comm_info_request` → empty comms

**Session state:**
- Code accumulates across cells in `SESSION_CODE_ALL: text`
- Output delta tracking via `SESSION_PREV_OUTPUT_LEN` (only returns new output)
- Failed cells rolled back to `SESSION_CODE_PREV`

**JSON parsing fix:** `extract_field()` rewritten to handle escaped quotes (`\"`) in JSON strings. Original implementation stopped at first `"` inside values, breaking code fields like `"print \"Hello\""`.

### 3. Python ZMQ Bridge (`tools/jupyter/kernel_wrapper.py` — 331 lines)

**Architecture:** Thin Python bridge handling:
- Connection file parsing (transport, ip, key, 5 ports)
- ZMQ socket setup (ROUTER for shell/control, PUB for iopub, REP for heartbeat)
- HMAC-SHA256 message signing
- Process spawning with `cwd=project_root`
- Message bridging: ZMQ multipart <-> stdin/stdout JSON-lines
- Background threads: heartbeat echo, control channel, stdout reader

### 4. Installation (`tools/jupyter/install.shs` — 69 lines)

Shell script that:
- Checks dependencies (python3, jupyter, pyzmq)
- Creates kernel directory in Jupyter data dir
- Generates `kernel.json` with absolute paths
- Verifies installation via `jupyter kernelspec list`

### 5. Docker E2E (`tools/docker/Dockerfile.jupyter-test` — 84 lines)

Ubuntu 24.04 + Python venv + Jupyter packages. Copies Simple binary, kernel source, wrapper, and test files. Runs `run_server_check.py` as entrypoint with non-root user.

---

## Test Results

### REPL System Tests — 19/19 passing

| Spec File | Tests | Status |
|-----------|-------|--------|
| `repl_basic_eval_system_spec.spl` | 5 | PASS |
| `repl_state_persistence_system_spec.spl` | 3 | PASS |
| `repl_multiline_system_spec.spl` | 2 | PASS |
| `repl_error_recovery_system_spec.spl` | 2 | PASS |
| `repl_commands_system_spec.spl` | 7 | PASS |

### Jupyter System Tests — 22/22 passing

| Spec File | Tests | Status |
|-----------|-------|--------|
| `jupyter_kernel_install_system_spec.spl` | 7 | PASS |
| `jupyter_execution_system_spec.spl` | 4 | PASS |
| `jupyter_state_system_spec.spl` | 2 | PASS |
| `jupyter_error_system_spec.spl` | 3 | PASS |
| `jupyter_notebook_server_system_spec.spl` | 6 | PASS |

### E2E Tests Executed

| Test | Method | Result |
|------|--------|--------|
| HTTP server start | `GET /api/status` on localhost:18889 | PASS |
| Kernel spec listing | `GET /api/kernelspecs` | PASS (Simple kernel found) |
| Session creation | `POST /api/sessions` | PASS (kernel_id returned) |
| ZMQ cell execution | `print "Hello from Simple!"` | PASS (output verified) |
| Cross-cell state | `val x = 42` then `print x` | PASS (output "42") |
| Docker container E2E | All 5 checks inside isolated container | PASS |
| nbconvert hello.ipynb | 3 cells: print, val+print, fn+call | PASS |
| nbconvert state_persistence.ipynb | 4 cells: val, print, fn def, fn call | PASS |

---

## Bugs Fixed During Implementation

1. **`extract_field` JSON parser** — didn't handle escaped quotes (`\"`) in JSON strings. Code like `print "Hello"` was extracted as `print \` because the first `\"` terminated extraction. Fixed with proper escape-aware parser loop.

2. **Output accumulation** — kernel re-runs entire accumulated program, so output included all previous cells' output. Fixed by tracking `SESSION_PREV_OUTPUT_LEN` and returning only the delta.

3. **Working directory** — `kernel_wrapper.py` spawned Simple process without `cwd`, so `bin/release/simple` (relative path in kernel) failed when Jupyter ran from a different directory. Fixed by setting `cwd=project_root`.

4. **Subprocess stdin inheritance** — when kernel reads JSON-lines from stdin, child `bin/release/simple` inherited the same stdin and consumed JSON data as code. Fixed by running via `bash -c "bin/release/simple path </dev/null 2>&1"`.

5. **Compiler import startup** — initial REPL imported `interpret_file()` from compiler, causing 40s+ startup. Fixed by removing all compiler imports, using subprocess-only evaluation.

6. **Module-level array methods** — `.push()` and `.len()` on module-level arrays caused "unsupported path call" errors. Fixed by using text concatenation instead of arrays.

---

## File Inventory (25 files, ~2,600 lines)

| Category | Files | Lines |
|----------|-------|-------|
| Source (REPL) | `src/app/repl/main.spl` | 249 |
| Source (Kernel) | `src/app/jupyter_kernel/{main,protocol,session}.spl` | 490 |
| Tools | `tools/jupyter/{kernel_wrapper.py,kernel.json,install.shs}` | 406 |
| Test specs (REPL) | `test/system/repl/*_spec.spl` (5 files) | 169 |
| Test specs (Jupyter) | `test/system/jupyter/*_spec.spl` (5 files) | 274 |
| Test helpers | `test/system/jupyter/helpers/*.py` (2 files) | 728 |
| Test fixtures | `test/system/jupyter/fixtures/*.ipynb` (2 files) | 113 |
| Docker/CI | `tools/docker/Dockerfile.jupyter-test`, `*.sdn`, `scripts/test/*.shs` | 182 |

---

## Documentation

| Document | Path |
|----------|------|
| REPL Guide | `doc/guide/tooling/repl.md` |
| Jupyter Guide | `doc/guide/tooling/jupyter.md` |
| Implementation Report | `doc/report/repl_jupyter_implementation_2026-03-11.md` |
| REPL Spec (updated) | `doc/spec/tooling/simple_repl.md` |
