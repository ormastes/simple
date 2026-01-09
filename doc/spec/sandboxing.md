# Sandboxing & Isolation

> **⚠️ MIGRATED:** This specification has been migrated to an executable test file:  
> **→** `tests/specs/sandboxing_spec.spl`  
> **Date:** 2026-01-09  
> 
> This file is kept for reference but may become outdated. The _spec.spl file is the source of truth.

**Status:** ✅ Runtime Complete (#916-919), 📋 Environment Planned (#920-923)
**Feature IDs:** #916-923
**Last Updated:** 2025-12-28
**Keywords:** sandbox, isolation, security, environment, virtualen

v, containers
**Topics:** security, tooling

Complete isolation system combining **runtime sandboxing** (process isolation like Docker containers) and **environment isolation** (dependency/package isolation like Python virtualenv). Enables safe development and execution of untrusted code.

## Related Specifications
- [BDD Testing](testing/testing_bdd_framework.md) - Test framework integration
- [Build Audit](build_audit.md) - Security auditing

---

## Contents

1. [Overview](#overview)
2. [Runtime Sandboxing (#916-919)](#runtime-sandboxing-916-919)
3. [Environment Isolation (#920-923)](#environment-isolation-920-923)
4. [Implementation](#implementation)
5. [Key Workflows](#key-workflows)
6. [Benefits for LLM Tools](#benefits-for-llm-tools)

---

## Overview

### Two Isolation Models

#### Environment Isolation (#920-923)
**Like Python virtualenv:**
- Isolate packages and dependencies per project
- Project-local package cache
- Reproducible dependency sets
- Fast activation/deactivation
- No process overhead

#### Runtime Sandboxing (#916-919)
**Like Docker containers:**
- Process isolation with namespaces
- Resource limits (CPU, memory, time)
- Network isolation
- Filesystem restrictions
- Secure execution of untrusted code

**Both work together:**
```bash
# Create environment
simple env create myproject

# Activate environment
simple env activate myproject

# Install packages in environment
simple pkg add http-client@1.0.0

# Run in sandboxed environment
simple run --sandbox app.spl
```

### Motivation

**Problems:**
1. **Dependency Conflicts** - Different projects need different package versions
2. **Package Pollution** - Global installs affect all projects
3. **Malicious Code** - LLM-generated code might be dangerous
4. **Resource Abuse** - Untrusted code can consume unlimited resources
5. **Network/Filesystem Access** - No restrictions on system access

**Solutions:**
1. **Environment Isolation** - Separate package environments per project
2. **Runtime Sandboxing** - Secure execution with limits and restrictions

---

## Runtime Sandboxing (#916-919)

**Status:** ✅ Complete

Runtime sandboxing provides **process-level isolation** for secure execution of untrusted code, similar to Docker containers.

### #916: Resource Limits (Difficulty: 3)

**CPU Time Limits:**
```bash
# Limit execution to 5 seconds
simple run --sandbox --time-limit=5s app.spl

# Limit to 100ms for tests
simple test --sandbox --time-limit=100ms
```

**Memory Limits:**
```bash
# Limit to 100MB
simple run --sandbox --memory-limit=100M app.spl

# Limit to 1GB
simple run --sandbox --memory-limit=1G app.spl
```

**Combined Limits:**
```bash
# Time + memory
simple run --sandbox \
  --time-limit=10s \
  --memory-limit=500M \
  app.spl
```

**Configuration File:**
```toml
# simple.toml
[sandbox]
time_limit = "5s"
memory_limit = "100M"
cpu_limit = 80        # Max 80% CPU usage
file_descriptors = 100
processes = 1         # No fork/exec
```

**Error Handling:**
```bash
# Time limit exceeded
simple run --sandbox --time-limit=1s infinite_loop.spl
Error: Execution exceeded time limit (1s)
Exit: 124

# Memory limit exceeded
simple run --sandbox --memory-limit=10M memory_hog.spl
Error: Memory limit exceeded (10M)
Exit: 125
```

### #917: Network Isolation (Difficulty: 4)

**Default: Network Disabled**
```bash
# Network completely blocked
simple run --sandbox app.spl

# Attempting network fails
fn main():
    http.get("https://example.com")  # Error: Network not allowed
```

**Allow Specific Domains:**
```bash
# Allow only specific domains
simple run --sandbox \
  --allow-network=example.com \
  --allow-network=api.github.com \
  app.spl

# Configuration
[sandbox.network]
allow_domains = ["example.com", "api.github.com"]
allow_ports = [443]  # HTTPS only
block_internal = true  # Block 127.0.0.1, 192.168.*, etc.
```

**Network Logging:**
```bash
# Log network attempts
simple run --sandbox --log-network app.spl

# Output
[SANDBOX] Network attempt blocked: http://evil.com
[SANDBOX] Network attempt blocked: https://internal-server
```

### #918: Filesystem Isolation (Difficulty: 4)

**Read-Only by Default:**
```bash
# All filesystem access denied
simple run --sandbox app.spl

fn main():
    fs.read_file("/etc/passwd")  # Error: Filesystem access denied
```

**Allow Specific Directories:**
```bash
# Allow read from specific directory
simple run --sandbox \
  --allow-read=/home/user/data \
  app.spl

# Allow write to output directory
simple run --sandbox \
  --allow-read=/input \
  --allow-write=/output \
  app.spl
```

**Temporary Directory:**
```bash
# Provide isolated temp directory
simple run --sandbox --temp-dir app.spl

# In code:
fn main():
    let temp = env.temp_dir()  # Isolated temp dir
    fs.write_file(temp + "/data.txt", "content")  # OK
    fs.write_file("/etc/hosts", "...")  # ERROR: denied
```

**Configuration:**
```toml
[sandbox.filesystem]
allow_read = ["/input", "/config"]
allow_write = ["/output", "/tmp"]
deny_patterns = ["/etc/*", "/sys/*", "/proc/*"]
max_file_size = "10M"
max_files = 100
```

### #919: `simple run --sandbox` (Difficulty: 2)

**Basic Usage:**
```bash
# Run in sandbox with defaults
simple run --sandbox app.spl

# Run with custom limits
simple run --sandbox \
  --time-limit=10s \
  --memory-limit=500M \
  --allow-network=api.example.com \
  --allow-read=/data \
  --allow-write=/output \
  app.spl
```

**Test Integration:**
```bash
# Run tests in sandbox
simple test --sandbox

# Sandbox with limits
simple test --sandbox \
  --time-limit=5s \
  --memory-limit=100M

# Configuration
[test]
sandbox = true
sandbox_time_limit = "5s"
sandbox_memory_limit = "100M"
```

**Profiles:**
```toml
# simple.toml
[sandbox.profiles.strict]
time_limit = "1s"
memory_limit = "10M"
allow_network = false
allow_filesystem = false

[sandbox.profiles.testing]
time_limit = "30s"
memory_limit = "500M"
allow_network = false
allow_read = ["test/fixtures"]
allow_write = ["test/output"]

[sandbox.profiles.development]
time_limit = "60s"
memory_limit = "2G"
allow_network = ["localhost", "*.local"]
allow_filesystem = true

# Use profile
$ simple run --sandbox=strict app.spl
$ simple test --sandbox=testing
```

**Logging & Monitoring:**
```bash
# Verbose sandbox logging
simple run --sandbox --sandbox-log=verbose app.spl

# Output:
[SANDBOX] Starting with profile: default
[SANDBOX] Time limit: 5s
[SANDBOX] Memory limit: 100M
[SANDBOX] Network: denied
[SANDBOX] Filesystem: read-only
[SANDBOX] Running: app.spl
[SANDBOX] CPU time: 0.123s (2.5%)
[SANDBOX] Memory: 15.2M (15%)
[SANDBOX] Exit: 0
```

---

## Environment Isolation (#920-923)

**Status:** 📋 Planned

Environment isolation provides **package and dependency isolation** per project, similar to Python virtualenv.

### #920: Environment Creation & Management (Difficulty: 2)

**Create Environment:**
```bash
# Create new environment
simple env create myproject
Created environment: /home/user/myproject/.simple/env

# Create with specific Simple version
simple env create myproject --simple-version=0.5.0

# List environments
simple env list
myproject     /home/user/myproject/.simple/env
shared-libs   /home/user/.simple/envs/shared-libs
global        /home/user/.simple/envs/global (default)
```

**Activate/Deactivate:**
```bash
# Activate environment
simple env activate myproject
# or source-based (like Python venv)
source .simple/env/bin/activate

# Environment is now active
(myproject) $ simple pkg list
http-client@1.0.0
json-parser@2.3.1

# Deactivate
(myproject) $ simple env deactivate
```

**Environment Detection:**
```bash
# Auto-detect from .simple/env/
cd myproject/
simple run app.spl   # Uses local environment automatically

# Auto-detect from simple.toml
[project]
environment = ".simple/env"

# Manual override
simple run --env=myproject app.spl
```

**Environment Structure:**
```
myproject/
├── .simple/
│   ├── env/                    # Environment root
│   │   ├── bin/                # Executables
│   │   │   ├── activate        # Bash activation
│   │   │   ├── activate.fish   # Fish activation
│   │   │   └── simple          # Simple binary
│   │   ├── lib/                # Installed packages
│   │   ├── cache/              # Local package cache
│   │   ├── simple.lock         # Locked dependencies
│   │   └── env.toml            # Environment config
│   └── temp/                   # Temporary files
└── simple.toml                 # Project config
```

### #921: Package Isolation (Difficulty: 3)

**Per-Environment Packages:**
```bash
# Activate environment
simple env activate myproject

# Install package (goes to environment)
simple pkg add http-client@1.0.0
Installing http-client@1.0.0 to /home/user/myproject/.simple/env/lib

# List packages in current environment
simple pkg list
http-client@1.0.0       /myproject/.simple/env/lib/http-client@1.0.0
json-parser@2.3.1       /myproject/.simple/env/lib/json-parser@2.3.1
```

**Dependency Resolution:**
```bash
# Add package with dependencies
simple pkg add web-framework@2.0.0

Resolving dependencies:
  web-framework@2.0.0
  ├── http-client@1.0.0
  ├── json-parser@2.3.1
  └── template-engine@1.5.0
      └── string-utils@3.2.0

Installing to environment: myproject
  5 packages, 12.3 MB

# Lock file created/updated
Created .simple/env/simple.lock
```

### #922: Environment Reproducibility (Difficulty: 2)

**Lock Files:**
```toml
# .simple/env/simple.lock
version = 1

[environment]
name = "myproject"
simple_version = "0.5.0"
created = 2025-12-24T10:30:00Z
updated = 2025-12-24T14:15:00Z

[[package]]
name = "http-client"
version = "1.0.0"
source = "registry+https://packages.simple-lang.org"
checksum = "sha256:a1b2c3d4..."
dependencies = ["socket-utils@2.1.0"]
```

**Recreate from Lock:**
```bash
# Clone project with simple.lock
git clone https://github.com/user/project
cd project

# Create environment from lock file
simple env create --from-lock
Reading .simple/env/simple.lock
Creating environment: project
Installing 12 packages...
✓ http-client@1.0.0
✓ socket-utils@2.1.0
✓ json-parser@2.3.1
...
Environment ready.

# Or with sync command
simple env sync
Syncing environment from simple.lock
No changes needed (all packages up-to-date)
```

**Deterministic Builds:**
```bash
# Verify environment matches lock
simple env verify
Verifying environment against simple.lock
✓ http-client@1.0.0 (checksum matches)
✓ socket-utils@2.1.0 (checksum matches)
✓ json-parser@2.3.1 (checksum matches)
All 12 packages verified.

# Detect drift
simple env verify
Warning: Environment has drifted from simple.lock
  http-client: 1.0.0 (lock) vs 1.0.1 (installed)
Run 'simple env sync' to fix.
```

### #923: Environment + Sandbox Integration (Difficulty: 2)

**Running in Sandboxed Environment:**
```bash
# Activate environment and run sandboxed
simple env activate myproject
simple run --sandbox app.spl

# Or combined syntax
simple run --env=myproject --sandbox app.spl

# Environment config with sandbox defaults
[environment.sandbox]
enabled = true
time_limit = "30s"
memory_limit = "500M"
allow_network = false
```

**Testing in Isolated Environment:**
```bash
# Run tests in environment + sandbox
simple test --env=myproject --sandbox

# CI/CD usage
simple env create ci-test --from-lock
simple run --env=ci-test --sandbox \
  --time-limit=60s \
  --memory-limit=1G \
  test_suite.spl
```

**Environment Profiles:**
```toml
# simple.toml
[environment.dev]
sandbox = false
allow_network = true

[environment.test]
sandbox = true
time_limit = "30s"
memory_limit = "500M"
allow_network = false

[environment.prod]
sandbox = true
profile = "strict"
allow_network = ["api.example.com"]
allow_read = ["/data"]
allow_write = ["/output"]

# Use with:
# simple run --env=dev app.spl      # No sandbox
# simple run --env=test app.spl     # Sandboxed testing
# simple run --env=prod app.spl     # Strict production
```

---

## Implementation

### Rust Dependencies

```toml
# Cargo.toml
[dependencies]
# Environment isolation
serde = { version = "1.0", features = ["derive"] }
toml = "0.8"                    # TOML parsing
walkdir = "2.4"                 # Directory traversal
shellexpand = "3.1"             # Shell variable expansion

# Sandbox - Cross-platform
rlimit = "0.10"                 # Resource limits

# Sandbox - Linux
[target.'cfg(target_os = "linux")'.dependencies]
nix = { version = "0.27", features = ["process", "sched", "resource", "mount"] }
seccompiler = "0.4"             # Seccomp filter (Firecracker)
caps = "0.5"                    # Linux capabilities

# Sandbox - Windows
[target.'cfg(windows)'.dependencies]
windows = { version = "0.52", features = [
    "Win32_System_JobObjects",
    "Win32_System_Threading",
] }

# Sandbox - macOS
[target.'cfg(target_os = "macos")'.dependencies]
libc = "0.2"                    # For sandbox-exec

# Docker backend
bollard = { version = "0.16", optional = true }
tokio = { version = "1.35", features = ["full"], optional = true }

[features]
docker = ["bollard", "tokio"]
```

### Platform-Specific Implementations

#### Linux (Namespaces + Seccomp)

Uses `nix` crate for namespaces (CLONE_NEWNET, CLONE_NEWPID, etc.) and `seccompiler` for syscall filtering. Provides strong isolation with user namespaces, resource limits via setrlimit, and fine-grained syscall control.

#### macOS (sandbox-exec)

Uses Apple's `sandbox-exec` system command with custom Sandbox Profile Language (SBPL). Provides filesystem isolation, process restrictions, and basic resource limits via setrlimit.

#### Windows (Job Objects)

Uses Win32 Job Objects API for process grouping and resource limits. Supports CPU time limits, memory limits, process limits, and UI restrictions. No syscall filtering equivalent.

#### Docker (Optional)

Uses `bollard` crate to interact with Docker daemon. Provides maximum isolation in containers with full network, filesystem, and process isolation. Higher overhead but universal across platforms.

### Library Usage Summary

| Platform | Libraries | Purpose |
|----------|-----------|---------|
| **All** | serde, toml, anyhow | Configuration & errors |
| **All** | walkdir, shellexpand | File traversal & paths |
| **All** | rlimit | Cross-platform limits |
| **Linux** | nix, seccompiler, caps | Namespaces & syscall filtering |
| **macOS** | libc | setrlimit calls |
| **Windows** | windows 0.52 | Job Objects API |
| **Docker** | bollard, tokio | Docker API client |

### Performance Comparison

```
Backend         Launch   Runtime   Memory    Use Case
────────────────────────────────────────────────────────
Native (Linux)  5-20ms   1-3%      1-10MB    Default, REPL, tests
Native (macOS)  10-30ms  2-4%      2-15MB    Default on Mac
Native (Windows) 8-25ms  2-5%      2-12MB    Default on Windows
Docker          200ms-3s  5-10%    100-500MB CI/CD, max isolation
```

### File Structure

```
src/runtime/src/
├── environment/        # Environment isolation
│   ├── mod.rs          # Environment manager
│   ├── config.rs       # env.toml handling
│   ├── lock.rs         # simple.lock handling
│   └── activation.rs   # Shell activation scripts
│
├── sandbox/            # Runtime sandboxing
│   ├── mod.rs          # Main sandbox API
│   ├── linux.rs        # Linux (namespaces + seccomp)
│   ├── macos.rs        # macOS (sandbox-exec)
│   ├── windows.rs      # Windows (job objects)
│   ├── limits.rs       # Resource limits
│   ├── network.rs      # Network filtering
│   └── filesystem.rs   # Filesystem restrictions
│
└── isolation/          # Integration layer
    ├── mod.rs          # Combined environment + sandbox
    └── profiles.rs     # Sandbox profiles per environment
```

---

## Key Workflows

**Development:**
```bash
simple env create myproject
simple env activate myproject
simple pkg add web-framework@2.0.0
simple run app.spl                     # Uses environment automatically
```

**Testing:**
```bash
simple test --env=test --sandbox       # Isolated + sandboxed
```

**Production:**
```bash
simple run --env=prod --sandbox=strict app.spl
```

**CI/CD:**
```bash
simple env create ci --from-lock
simple run --env=ci --sandbox --time-limit=60s test_suite.spl
```

---

## Benefits for LLM Tools

### Environment Isolation Benefits:
1. **No Dependency Conflicts** - Each project has its own packages
2. **Reproducible Builds** - Lock files ensure consistency
3. **Easy Onboarding** - `simple env create --from-lock` sets up everything
4. **Clean Development** - No global package pollution
5. **Version Testing** - Multiple environments with different versions

### Runtime Sandboxing Benefits:
1. **Safe Verification** - Test untrusted code without risk
2. **Resource Control** - Prevent infinite loops/memory leaks
3. **Network Safety** - Block unauthorized external access
4. **Filesystem Protection** - Prevent data corruption
5. **CI/CD Integration** - Consistent, isolated test environments

### Combined Benefits:
1. **Complete Isolation** - Dependencies + execution both isolated
2. **Security Layers** - Package isolation + runtime restrictions
3. **Developer Experience** - Like Python venv + Docker combined
4. **LLM-Friendly** - Safe testing of generated code with controlled dependencies

---

## Related Features

**Environment Isolation:**
- Package manager (#1-8): Base infrastructure for dependency management
- Module system: Import resolution with environment packages
- Project detection: Auto-detect environments from `simple.toml`

**Runtime Sandboxing:**
- #880-884: Capability effects (enforced by sandbox)
- #894-898: Property testing (run in sandbox)
- #906-907: Lint (detect unsafe operations)

**Integration:**
- Test framework: Run tests in isolated environments
- CI/CD: Reproducible builds with environment + sandbox
- LSP/DAP: Environment-aware development tools

---

## Summary

This specification covers **8 features (#916-923)** providing complete isolation for Simple projects:

### Runtime Sandboxing (Container-Style) - #916-919
**Like Docker:** Process isolation, resource limits, security restrictions
- #916: Resource limits (CPU, memory, time) ✅
- #917: Network isolation (block/allowlist) ✅
- #918: Filesystem isolation (read/write restrictions) ✅
- #919: `simple run --sandbox` CLI ✅

### Environment Isolation (Virtualenv-Style) - #920-923
**Like Python's venv:** Dependency isolation, project-local packages, reproducible builds
- #920: Environment creation & management 📋
- #921: Package isolation 📋
- #922: Environment reproducibility (lock files) 📋
- #923: Environment + sandbox integration 📋

This provides the **best of both worlds**: dependency isolation (like Python venv) + runtime security (like containers), making Simple ideal for LLM-assisted development with safe execution of generated code.
