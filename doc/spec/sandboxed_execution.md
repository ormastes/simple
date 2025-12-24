# Sandboxed Execution Specification (#916-919)

**Status:** 📋 Planned  
**Category:** LLM-Friendly Features  
**Priority:** Medium  
**Difficulty:** 2-4

## Overview

Sandboxed execution environment for safely running LLM-generated code with resource limits, network isolation, and filesystem restrictions. Enables verification without risk.

## Motivation

**Problem:**
- LLM-generated code might be malicious
- Testing untrusted code is dangerous
- No limits on resource usage
- Network/filesystem access unrestricted

**Solution:**
- Run code in isolated sandbox
- Enforce CPU/memory/time limits
- Block network access by default
- Restrict filesystem to specific directories
- Safe verification of LLM output

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

## Implementation

### Linux (Primary)

**Using `seccomp` + `cgroups` + `namespaces`:**

```rust
use nix::sched::{unshare, CloneFlags};
use nix::sys::resource::{setrlimit, Resource};
use seccompiler::SeccompFilter;

pub struct Sandbox {
    time_limit: Duration,
    memory_limit: usize,
    network_allowed: bool,
    fs_allowed: Vec<PathBuf>,
}

impl Sandbox {
    pub fn run<F>(&self, f: F) -> Result<()>
    where
        F: FnOnce() -> Result<()>,
    {
        // Create new namespaces
        unshare(
            CloneFlags::CLONE_NEWNET |  // Network namespace
            CloneFlags::CLONE_NEWPID |  // PID namespace
            CloneFlags::CLONE_NEWNS     // Mount namespace
        )?;
        
        // Set resource limits
        self.set_resource_limits()?;
        
        // Apply seccomp filter
        self.apply_seccomp_filter()?;
        
        // Set up filesystem restrictions
        self.setup_filesystem()?;
        
        // Run the code
        let start = Instant::now();
        let result = f();
        let elapsed = start.elapsed();
        
        // Check time limit
        if elapsed > self.time_limit {
            return Err(SandboxError::TimeLimitExceeded);
        }
        
        result
    }
    
    fn set_resource_limits(&self) -> Result<()> {
        // CPU time limit
        let rlim = rlimit {
            rlim_cur: self.time_limit.as_secs(),
            rlim_max: self.time_limit.as_secs(),
        };
        setrlimit(Resource::RLIMIT_CPU, &rlim)?;
        
        // Memory limit
        let mem_rlim = rlimit {
            rlim_cur: self.memory_limit,
            rlim_max: self.memory_limit,
        };
        setrlimit(Resource::RLIMIT_AS, &mem_rlim)?;
        
        // File descriptor limit
        let fd_rlim = rlimit {
            rlim_cur: 100,
            rlim_max: 100,
        };
        setrlimit(Resource::RLIMIT_NOFILE, &fd_rlim)?;
        
        Ok(())
    }
    
    fn apply_seccomp_filter(&self) -> Result<()> {
        let mut filter = SeccompFilter::new();
        
        // Allow basic syscalls
        filter.allow_syscall("read");
        filter.allow_syscall("write");
        filter.allow_syscall("open");
        filter.allow_syscall("close");
        filter.allow_syscall("brk");
        filter.allow_syscall("mmap");
        
        // Block network syscalls if disabled
        if !self.network_allowed {
            filter.deny_syscall("socket");
            filter.deny_syscall("connect");
            filter.deny_syscall("bind");
        }
        
        // Apply filter
        filter.load()?;
        Ok(())
    }
}
```

### macOS

**Using `sandbox-exec`:**

```rust
// macOS implementation using sandbox profiles
fn run_sandboxed_macos(cmd: &str) -> Result<()> {
    let profile = r#"
        (version 1)
        (deny default)
        (allow process-exec (literal "{cmd}"))
        (allow file-read* (subpath "/usr/lib"))
        (allow file-read* (subpath "/System"))
        "#;
    
    std::process::Command::new("sandbox-exec")
        .arg("-p")
        .arg(profile)
        .arg(cmd)
        .spawn()?;
    
    Ok(())
}
```

### Windows

**Using Job Objects:**

```rust
// Windows implementation using job objects
#[cfg(windows)]
fn run_sandboxed_windows(cmd: &str) -> Result<()> {
    use winapi::um::jobapi2::*;
    use winapi::um::winnt::*;
    
    unsafe {
        let job = CreateJobObjectW(null_mut(), null_mut());
        
        // Set limits
        let mut limits: JOBOBJECT_EXTENDED_LIMIT_INFORMATION = zeroed();
        limits.BasicLimitInformation.LimitFlags = 
            JOB_OBJECT_LIMIT_PROCESS_TIME |
            JOB_OBJECT_LIMIT_JOB_MEMORY;
        limits.BasicLimitInformation.PerProcessUserTimeLimit = time_limit_100ns;
        limits.JobMemoryLimit = memory_limit_bytes;
        
        SetInformationJobObject(
            job,
            JobObjectExtendedLimitInformation,
            &mut limits as *mut _ as *mut _,
            size_of::<JOBOBJECT_EXTENDED_LIMIT_INFORMATION>() as u32,
        );
        
        // Assign process to job
        AssignProcessToJobObject(job, process_handle);
    }
    
    Ok(())
}
```

## Benefits for LLM Tools

1. **Safe Verification** - Test untrusted code without risk
2. **Resource Control** - Prevent infinite loops/memory leaks
3. **Network Safety** - Block unauthorized external access
4. **Filesystem Protection** - Prevent data corruption
5. **Reproducibility** - Consistent test environment

## Implementation Plan

### Phase 1: Resource Limits (2 days)
- [ ] Time limit enforcement
- [ ] Memory limit enforcement
- [ ] CPU usage limits
- [ ] Tests for limits

### Phase 2: Network Isolation (2 days)
- [ ] Block all network by default
- [ ] Allowlist implementation
- [ ] Domain filtering
- [ ] Tests for network isolation

### Phase 3: Filesystem Isolation (2 days)
- [ ] Block all filesystem by default
- [ ] Allow specific directories
- [ ] Virtual filesystem overlay
- [ ] Tests for filesystem isolation

### Phase 4: CLI Integration (1 day)
- [ ] `--sandbox` flag
- [ ] Profile system
- [ ] Configuration file support
- [ ] Documentation

**Total Estimated Effort:** 7 days

## File Structure

```
src/runtime/src/sandbox/
├── mod.rs              # Main sandbox API
├── linux.rs            # Linux implementation (seccomp)
├── macos.rs            # macOS implementation (sandbox-exec)
├── windows.rs          # Windows implementation (job objects)
├── limits.rs           # Resource limits
├── network.rs          # Network filtering
└── filesystem.rs       # Filesystem restrictions

tests/sandbox/
├── limits_spec.rs      # Resource limit tests
├── network_spec.rs     # Network isolation tests
└── filesystem_spec.rs  # Filesystem isolation tests
```

## Related Features

- #880-884: Capability effects (enforced by sandbox)
- #894-898: Property testing (run in sandbox)
- #906-907: Lint (detect unsafe operations)

## Success Metrics

- [ ] 100% of malicious code contained
- [ ] Zero false positives (legitimate code runs)
- [ ] <5% performance overhead
- [ ] Works on Linux, macOS, Windows
- [ ] 95%+ developer satisfaction

## References

- **Docker** - Container isolation
- **Firejail** - Linux sandbox
- **systemd-run** - Resource limits
- **seccomp** - Syscall filtering

---

**Next Steps:**
1. Review and approve specification
2. Implement Linux version first
3. Add macOS and Windows support
4. Test with LLM-generated code
5. Mark #916-919 complete
