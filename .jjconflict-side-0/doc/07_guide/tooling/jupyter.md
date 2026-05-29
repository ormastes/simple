# Jupyter Kernel Guide

Run Simple language code in Jupyter notebooks, JupyterLab, and Jupyter console.

---

## Quick Start

### Install the Kernel

```bash
sh tools/jupyter/install.shs
```

This registers the Simple kernel with Jupyter. Verify:

```bash
jupyter kernelspec list
# Available kernels:
#   simple    /home/user/.local/share/jupyter/kernels/simple
#   python3   /usr/lib/python3/dist-packages/ipykernel/resources
```

### Use in Jupyter Notebook

```bash
jupyter notebook
# Browser opens -> New -> Simple
```

### Use in Jupyter Console

```bash
jupyter console --kernel simple
```

### Use in JupyterLab

```bash
jupyter lab
# New Launcher -> Simple
```

---

## Prerequisites

```bash
# Python packages
pip install notebook jupyter_client pyzmq

# Simple runtime must be built or deployed
bin/simple build --release
```

---

## Notebook Usage

Create a new notebook with the "Simple" kernel. Each cell runs Simple code:

**Cell 1:**
```simple
val greeting = "Hello from Simple!"
print greeting
```
Output: `Hello from Simple!`

**Cell 2:**
```simple
fn factorial(n: i64) -> i64:
    if n <= 1:
        return 1
    n * factorial(n - 1)

print factorial(10)
```
Output: `3628800`

**Cell 3 (uses state from Cell 1):**
```simple
print greeting
```
Output: `Hello from Simple!`

---

## How It Works

### Architecture

```
Jupyter Client (browser/console)
    |
    v  (ZMQ wire protocol)
kernel_wrapper.py (Python ZMQ bridge)
    |
    v  (stdin/stdout JSON-lines)
Simple Kernel (src/app/jupyter_kernel/main.spl)
    |
    v  (subprocess)
bin/simple or bin/release/<platform>/simple (executes accumulated code)
```

### Message Flow

1. Jupyter sends ZMQ multipart message (execute_request)
2. Python wrapper deserializes to JSON-line, writes to kernel's stdin
3. Simple kernel extracts code, appends to session state, executes via subprocess
4. Output captured, sent as JSON-line to stdout
5. Python wrapper reconstructs ZMQ message, sends on iopub/shell channels

### Session State

All cells in a notebook share a session. Code accumulates across cells:

| Cell | Code | Accumulated Program |
|------|------|-------------------|
| 1 | `val x = 42` | `val x = 42` |
| 2 | `print x` | `val x = 42\nprint x` |
| 3 | `fn f(): x * 2` | `val x = 42\nprint x\nfn f(): x * 2` |

Only **new** output from each execution is shown (delta from previous output).

Failed cells are rolled back — accumulated state is preserved.

---

## Supported Message Types

| Message Type | Description |
|-------------|-------------|
| `kernel_info_request` | Returns language info, protocol version |
| `execute_request` | Execute code cell, return output/error |
| `is_complete_request` | Check if code is complete (lines ending `:` = incomplete) |
| `shutdown_request` | Shut down kernel |
| `comm_info_request` | Return empty comms (no widgets) |

---

## Kernel Spec

`tools/jupyter/kernel.json`:
```json
{
    "display_name": "Simple",
    "language": "simple",
    "argv": ["python3", "<path>/kernel_wrapper.py", "-f", "{connection_file}"],
    "file_extension": ".spl"
}
```

---

## Testing

### Run E2E Tests Locally

```bash
# Full server E2E (starts real Jupyter server, HTTP + ZMQ)
python3 test/system/jupyter/helpers/run_server_check.py

# Execute notebook via nbconvert
python3 test/system/jupyter/helpers/run_notebook_server_test.py \
    --notebook test/system/jupyter/fixtures/hello.ipynb --skip-server
```

### Run E2E Tests in Docker

```bash
# Build and run isolated container test
sh scripts/test/jupyter-docker-test.shs
```

### Run Spec Tests

```bash
# All Jupyter specs
bin/simple test test/system/jupyter/

# Individual specs
bin/simple test test/system/jupyter/jupyter_notebook_server_system_spec.spl
bin/simple test test/system/jupyter/jupyter_kernel_install_system_spec.spl
bin/simple test test/system/jupyter/jupyter_execution_system_spec.spl
```

### Test Coverage

| Test | What It Verifies |
|------|-----------------|
| Server E2E | HTTP `/api/status`, `/api/kernelspecs`, `/api/sessions`, ZMQ cell execution |
| Docker E2E | Same as above, inside isolated container |
| nbconvert hello.ipynb | 3 cells: print, val+print, fn+call |
| nbconvert state_persistence.ipynb | 4 cells: val, print, fn def, fn call (cross-cell state) |
| Kernel install | kernel.json, wrapper.py, install script |
| Execution | kernel_info, shutdown, is_complete |
| State | Code accumulation, error rollback |
| Error handling | Syntax errors, recovery, comm_info |

---

## Source Files

| File | Lines | Purpose |
|------|-------|---------|
| `src/app/jupyter_kernel/main.spl` | 288 | Kernel process (JSON-lines protocol) |
| `tools/jupyter/kernel_wrapper.py` | 331 | Python ZMQ bridge |
| `tools/jupyter/kernel.json` | 6 | Kernel spec template |
| `tools/jupyter/install.shs` | 69 | Installation script |
| `tools/docker/Dockerfile.jupyter-test` | 84 | Docker E2E image |
| `scripts/test/jupyter-docker-test.shs` | 72 | Docker test runner |

---

## Troubleshooting

**Kernel not found in Jupyter:**
```bash
# Re-install
sh tools/jupyter/install.shs
# Verify
jupyter kernelspec list | grep simple
```

**Kernel dies immediately:**
```bash
# Check Simple binary exists
ls -la bin/simple
# Test kernel directly
echo '{"msg_type":"kernel_info_request","msg_id":"t1","session":"s1","content":{}}' | \
    bin/simple run src/app/jupyter_kernel/main.spl
```

**Missing Python dependencies:**
```bash
pip install notebook jupyter_client pyzmq nbconvert
```

---

## Related

- [REPL Guide](repl.md) — interactive command-line REPL
- [LSP/DAP Guide](lsp_dap.md) — editor integration
- [Container Testing Guide](../testing/container_testing.md) — Docker test patterns
