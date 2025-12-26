# Runtime Sandboxing (#916-919)

**Part of:** [Sandboxed Execution](sandboxed_execution.md)
**Status:** ✅ Complete
**Category:** LLM-Friendly Features

## Overview

Runtime sandboxing provides **process-level isolation** for secure execution of untrusted code, similar to Docker containers. This includes resource limits, network isolation, and filesystem restrictions.

**Like Docker containers:**
- Process isolation with namespaces
- Resource limits (CPU, memory, time)
- Network isolation
- Filesystem restrictions
- Secure execution of untrusted code

## Features

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

# CPU limit exceeded
simple run --sandbox --cpu-limit=50 cpu_intensive.spl
Warning: CPU usage throttled to 50%
```

### #917: Network Isolation (Difficulty: 4)

**Default: Network Disabled**
```bash
# Network completely blocked
simple run --sandbox app.spl

# Attempting network fails
fn main():
    http.get("https://example.com")  # Error: Network not allowed

# Error output:
Runtime error: Network access denied in sandbox mode
  at http.get (http.spl:45)
  at main (app.spl:3)
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

**Allowlist Patterns:**
```toml
[sandbox.network]
allow_patterns = [
  "*.github.com",
  "api.*.com",
  "https://trusted-cdn.example.com/*"
]
deny_patterns = [
  "*.internal",
  "localhost",
  "127.*",
  "192.168.*"
]
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

**Virtual Filesystem:**
```bash
# Mount virtual overlay
simple run --sandbox \
  --virtual-fs \
  --mount=/data:/sandbox/data:ro \
  --mount=/output:/sandbox/output:rw \
  app.spl

# Code sees /sandbox/* paths only
fn main():
    let data = fs.read_file("/sandbox/data/input.txt")  # OK
    fs.write_file("/sandbox/output/result.txt", data)  # OK
    fs.write_file("/real/path", "...")  # ERROR: path not mounted
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

## See Also

- [Environment Isolation](sandbox_environment.md) - Package and dependency isolation
- [Implementation Details](sandbox_implementation.md) - Technical implementation
- [Sandboxed Execution Overview](sandboxed_execution.md) - Complete specification
