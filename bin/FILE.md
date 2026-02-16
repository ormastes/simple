# bin/ Directory Documentation

**Purpose:** Executable binaries, CLI wrappers, and MCP servers
**Total Size:** ~410MB (mostly multi-platform release binaries)
**Files:** 11 executable files + 5 subdirectories

---

## 📋 Quick Reference

| File | Purpose | When to Use |
|------|---------|-------------|
| `simple` | Main CLI wrapper | Primary entry point for all commands |
| `simple_mcp_server` | Full MCP server | Claude Code integration (33 tools) |
| `simple_mcp_server_lite` | Lite MCP server | Fast startup MCP (~10ms, core tools only) |
| `simple_mcp_fileio` | File I/O MCP server | Protected file operations |
| `simple-torch` | PyTorch wrapper | ML/tensor operations with PyTorch |
| `task` | Task CLI | AI assistant dispatcher |

---

## 🔧 Core Executables

### `simple` (6.5KB shell script)
**Main CLI wrapper and platform detector**

Automatically detects platform (Linux/macOS/FreeBSD/Windows × x86_64/ARM64/RISC-V) and uses appropriate bootstrap binary from `release/`.

**Features:**
- Multi-platform support (9 architectures)
- Fast-path optimization for common commands (~160ms faster)
- Stderr filtering (removes debug noise)
- Version detection from `VERSION` file
- Stdlib path optimization (eliminates 78+ path probes)

**Usage:**
```bash
bin/simple run file.spl           # Run Simple code
bin/simple build file.spl         # Compile to native
bin/simple test path/to/spec.spl  # Run tests
bin/simple --version              # Show version
bin/simple -c "print 'hello'"     # Eval code
```

**Fast-path commands:**
- `test` → `test_runner_new/test_runner_main.spl`
- `compile` → `compile_entry.spl`
- `lint`, `fmt`, `fix` → `lint_entry.spl`
- `bootstrap-check` → `bootstrap_check.spl`

**Environment Variables:**
- `SIMPLE_LIB` - Stdlib path (set automatically to `../src`)
- `SIMPLE_VERSION` - Version from VERSION file
- `SIMPLE_COMPILE_RUST=1` - Use Cranelift backend for compilation

---

## 🔌 MCP Servers (Model Context Protocol)

### `simple_mcp_server` (764 bytes wrapper)
**Full-featured MCP server for Claude Code integration**

**Entry Point:** `src/app/mcp/main.spl` (662 lines, 33 tools)

**Features:**
- **Debug tools (16):** Session management, breakpoints, stepping, variable inspection
- **Debug log tools (6):** AOP-based logging with enable/disable/query
- **Diagnostic read tools (4):** Read files, check syntax, list symbols, show status
- **Diagnostic edit tools (3):** Edit files, multi-edit, run code
- **Diagnostic VCS tools (4):** Diff, log, squash, new commits (jj)

**Startup:** ~50-100ms (full tool initialization)

**Configuration:** Add to Claude Code MCP config:
```json
{
  "mcpServers": {
    "simple": {
      "command": "/path/to/simple/bin/simple_mcp_server",
      "env": {
        "SIMPLE_LIB": "/path/to/simple/src"
      }
    }
  }
}
```

**Protocol:** JSON-RPC over stdio, auto-detects JSON Lines vs Content-Length

**Error Handling:**
- Stderr suppressed (`2>/dev/null`)
- `RUST_LOG=error` for minimal logging
- Clean JSON-RPC on stdout

---

### `simple_mcp_server_lite` (552 bytes wrapper)
**Lightweight MCP server with fast startup**

**Entry Point:** `src/app/mcp/main_lite.spl` (386 lines, core tools only)

**Features:**
- Fast startup (~10ms)
- Direct extern FFI calls
- No heavy module imports
- Core file/search tools only

**When to Use:**
- Frequent server restarts
- Resource-constrained environments
- Only need basic file operations

**Trade-offs:**
- ❌ No debug session tools
- ❌ No AOP logging tools
- ❌ Limited VCS integration
- ✅ 5x faster startup
- ✅ Lower memory usage

---

### `simple_mcp_fileio` (786 bytes wrapper)
**Specialized MCP server for protected file operations**

**Entry Point:** `src/app/mcp/fileio_main.spl` (719 lines)

**Features:**
- Protected file I/O operations
- Sandboxed file access
- Directory traversal prevention
- Safe file handling patterns

**When to Use:**
- Untrusted file operations
- Sandboxed environments
- Security-sensitive contexts

---

## 🧰 Utility Executables

### `simple-torch` (864 bytes)
**PyTorch FFI integration wrapper**

Runs Simple code with PyTorch tensor operations.

**Entry Point:** `src/app/torch/main.spl`

**Usage:**
```bash
bin/simple-torch run model.spl
```

**Features:**
- PyTorch tensor FFI bindings
- GPU acceleration support
- Neural network operations
- Automatic tensor type conversion

---

### `task` (279 bytes)
**AI assistant task dispatcher**

**Entry Point:** `src/app/task/main.spl`

**Usage:**
```bash
bin/task "implement feature X"
bin/task --list
```

Delegates to Simple's task app for AI-assisted development tasks.

---

## 🔗 Shared Libraries

### `libflush_stdout.so` (16KB)
**Force stdout line buffering**

LD_PRELOAD library that forces stdout to flush after every write.

**Usage:**
```bash
LD_PRELOAD=bin/libflush_stdout.so ./my_program
```

**Use Cases:**
- MCP servers (ensure prompt JSON-RPC delivery)
- Real-time log streaming
- Interactive applications

---

### `libunbuf.so` (16KB)
**Disable stdio buffering**

LD_PRELOAD library that makes stdout/stderr unbuffered.

**Usage:**
```bash
LD_PRELOAD=bin/libunbuf.so ./my_program
```

**Use Cases:**
- Debugging buffering issues
- Real-time output requirements
- Crash recovery (ensure all output written)

---

## 📁 Subdirectories

### `release/` (335MB)
**Multi-platform release binaries**

Contains pre-built Simple runtime for all supported platforms:

```
release/
├── simple                      # Main binary (Linux x86_64)
├── simple-0.5.0                # Version 0.5.0
├── simple-bootstrap-*.spk      # Bootstrap packages
├── linux-x86_64/simple         # Linux x86_64
├── linux-arm64/simple          # Linux ARM64
├── linux-riscv64/simple        # Linux RISC-V 64
├── macos-x86_64/simple         # macOS Intel
├── macos-arm64/simple          # macOS Apple Silicon
├── freebsd-x86/simple          # FreeBSD 32-bit
├── freebsd-x86_64/simple       # FreeBSD 64-bit
├── windows-x86/simple.exe      # Windows 32-bit
├── windows-x86_64/simple.exe   # Windows 64-bit
└── windows-arm64/simple.exe    # Windows ARM64
```

**Size:** Each binary is ~27MB (optimized release build)

**Purpose:**
- Multi-platform distribution
- No compilation required for end users
- CI/CD cross-platform testing

**Usage:** Automatically selected by `bin/simple` wrapper based on platform detection.

---

### `bootstrap/` (empty directories)
**Bootstrap compiler intermediate artifacts**

```
bootstrap/
├── seed/       # Seed compiler (C++ bootstrap)
├── core/       # Core library bootstrap
├── core1/      # Stage 1 core
├── core2/      # Stage 2 core
└── full1/      # Full bootstrap stage 1
```

**Purpose:**
- Multi-stage bootstrap compilation
- Self-hosting compiler development
- Build artifact caching

**Note:** These directories are created during bootstrap builds and contain intermediate `.o`, `.so`, and compiled modules.

---

### `mold/` (42MB)
**Mold linker binaries and libraries**

High-performance linker used for fast native compilation.

**Contents:**
- Mold linker executables
- Linker scripts
- Library dependencies

**Purpose:**
- 5-10x faster linking than GNU ld
- Parallel linking for large projects
- Used by Simple's native backend

**Usage:** Automatically invoked by compiler when available.

---

### `freebsd/` (32MB)
**FreeBSD-specific binaries and libraries**

FreeBSD platform support files and compatibility layers.

**Contents:**
- FreeBSD runtime binaries
- Linuxulator compatibility
- Platform-specific libraries

**Purpose:**
- Native FreeBSD support
- BSD system calls
- Cross-platform development

---

## 🎯 Common Workflows

### Development
```bash
# Run Simple code
bin/simple run my_program.spl

# Run tests
bin/simple test test/unit/my_spec.spl

# Build to native binary
bin/simple build my_program.spl -o my_program
./my_program
```

### Claude Code Integration
```bash
# Start MCP server (full)
bin/simple_mcp_server

# Start MCP server (lite, fast)
bin/simple_mcp_server_lite

# Debug MCP server
bin/mcp_proxy.py --port 8080
curl http://localhost:8080/initialize
```

### PyTorch ML Development
```bash
# Run PyTorch model
bin/simple-torch run model.spl

# Run training script
bin/simple-torch examples/07_ml/torch/training/basic.spl
```

### Task Automation
```bash
# Run AI task
bin/task "refactor module X to use struct instead of dict"

# List available tasks
bin/task --list
```

---

## 🔬 Technical Details

### Platform Detection Algorithm

1. Detect architecture: `uname -m`
   - x86_64, amd64 → `x86_64`
   - aarch64, arm64 → `arm64`
   - riscv64 → `riscv64`

2. Detect OS: `uname -s`
   - Linux → `linux`
   - Darwin → `macos`
   - FreeBSD → `freebsd`
   - MINGW/MSYS/Cygwin → `windows`

3. Find binary: `release/{os}-{arch}/simple`

4. Fallbacks:
   - FreeBSD x86_64 → Linux x86_64 (Linuxulator)
   - Generic → `release/simple` (Linux x86_64)

### Fast-Path Optimization

Standard command:
```
bin/simple test file.spl
→ loads main.spl (200+ lines)
→ loads all CLI modules (~2000 lines)
→ loads test runner (~160ms overhead)
```

Fast-path:
```
bin/simple test file.spl
→ directly loads test_runner_main.spl
→ skips CLI module loading
→ saves ~160ms per invocation
```

**Fast-path commands:** test, compile, lint, fmt, fix, bootstrap-check

### MCP Protocol Modes

**JSON Lines Mode:**
```
{"jsonrpc":"2.0","method":"initialize",...}\n
{"jsonrpc":"2.0","method":"tools/list",...}\n
```

**Content-Length Mode:**
```
Content-Length: 123\r\n\r\n
{"jsonrpc":"2.0","method":"initialize",...}
```

Simple MCP servers auto-detect protocol mode based on first message.

---

## 🚧 Removed Files (Cleanup 2026-02-16)

These files were removed during consolidation:

### Duplicates
- ❌ `simple_mcp_server_optimized` - Identical to simple_mcp_server
- ❌ `simple_mcp_server_legacy` - Old version
- ❌ `simple_mcp_server_native` - Requires manual compilation

### Legacy Binaries (371MB freed!)
- ❌ `srt2` - 371MB debug runtime (2026-01-01)
- ❌ `simple_v050` - Old version wrapper

### Broken Wrappers
- ❌ `simple_coverage` - Referenced non-existent simple_runtime
- ❌ `simple_stub` - Referenced non-existent simple_runtime

### Moved to scripts/
- 🔄 `build-minimal-bootstrap.sh` → `scripts/build/`
- 🔄 `verify-torch-ffi` → `scripts/test/`

---

## 📦 Installation

Release binaries are pre-built. To update:

```bash
# Download latest release
curl -L https://github.com/simple-lang/simple/releases/latest/download/simple-linux-x86_64 -o bin/release/simple
chmod +x bin/release/simple

# Verify
bin/simple --version
```

Multi-platform:
```bash
# Linux ARM64
curl -L .../simple-linux-arm64 -o bin/release/linux-arm64/simple

# macOS Apple Silicon
curl -L .../simple-macos-arm64 -o bin/release/macos-arm64/simple
```

---

## 🐛 Troubleshooting

### "No Simple runtime found"
**Cause:** Missing release binary for your platform

**Fix:**
```bash
# Check what platform detected
uname -s && uname -m

# Download for your platform
curl -L https://github.com/simple-lang/simple/releases/latest/download/simple-{os}-{arch} -o bin/release/simple
chmod +x bin/release/simple
```

### MCP server not responding
**Cause:** Stderr noise interfering with JSON-RPC

**Fix:** Use quiet wrapper:
```bash
bin/mcp_quiet.sh
```

Or manually suppress:
```bash
RUST_LOG=error bin/simple_mcp_server 2>/dev/null
```

### "symbol lookup error: libflush_stdout.so"
**Cause:** Library architecture mismatch

**Fix:** Rebuild library:
```bash
gcc -shared -fPIC -o bin/libflush_stdout.so -x c - <<'EOF'
#define _GNU_SOURCE
#include <stdio.h>
void __attribute__((constructor)) init() {
    setvbuf(stdout, NULL, _IOLBF, 0);
}
EOF
```

### Slow startup (>500ms)
**Cause:** Module path probing

**Fix:** Set SIMPLE_LIB:
```bash
export SIMPLE_LIB=/path/to/simple/src
bin/simple run file.spl  # Much faster
```

---

## 📚 See Also

- **MCP Implementation:** `src/app/mcp/`
- **CLI Implementation:** `src/app/cli/`
- **Build System:** `CLAUDE.md` - Build commands
- **Installation:** `install.sh` - Installation script
- **Version Control:** Use `jj` not `git` (see CLAUDE.md)

---

**Last Updated:** 2026-02-16
**Cleanup Freed:** 371MB
**Files Before:** 30+
**Files After:** 11
