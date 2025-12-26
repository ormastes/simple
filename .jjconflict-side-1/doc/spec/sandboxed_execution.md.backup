# Sandboxed Execution Specification (#916-923)

**Status:** 📋 Planned
**Category:** LLM-Friendly Features
**Priority:** Medium
**Difficulty:** 2-4

## Overview

Complete isolation system combining **environment isolation** (dependency/package isolation like Python virtualenv) and **runtime sandboxing** (process isolation like Docker containers). Enables safe development and execution of untrusted code.

## Two Isolation Models

### Environment Isolation (#920-923)
**Like Python virtualenv:**
- Isolate packages and dependencies per project
- Project-local package cache
- Reproducible dependency sets
- Fast activation/deactivation
- No process overhead

### Runtime Sandboxing (#916-919)
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

## Motivation

**Problems:**
1. **Dependency Conflicts** - Different projects need different package versions
2. **Package Pollution** - Global installs affect all projects
3. **Malicious Code** - LLM-generated code might be dangerous
4. **Resource Abuse** - Untrusted code can consume unlimited resources
5. **Network/Filesystem Access** - No restrictions on system access

**Solutions:**
1. **Environment Isolation** - Separate package environments per project
2. **Runtime Sandboxing** - Secure execution with limits and restrictions

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

---

## Part 2: Environment Isolation (Virtualenv-Style)

### #920: Environment Creation & Management (Difficulty: 2)

**Create Environment:**
```bash
# Create new environment
simple env create myproject
Created environment: /home/user/myproject/.simple/env

# Create with specific Simple version
simple env create myproject --simple-version=0.5.0

# Create with Python venv-style activation
simple env create myproject --with-activation-script

# List environments
simple env list
myproject     /home/user/myproject/.simple/env
shared-libs   /home/user/.simple/envs/shared-libs
global        /home/user/.simple/envs/global (default)
```

**Activate/Deactivate:**
```bash
# Activate environment (shell-specific)
simple env activate myproject
# or source-based (like Python venv)
source .simple/env/bin/activate

# Environment is now active
(myproject) $ simple pkg list
http-client@1.0.0
json-parser@2.3.1

# Deactivate
(myproject) $ simple env deactivate
# or
(myproject) $ deactivate
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

**Environment Info:**
```bash
# Show active environment
simple env info
Environment: myproject
Location: /home/user/myproject/.simple/env
Simple version: 0.5.0
Packages: 12 installed
Size: 45.3 MB

# Show specific environment
simple env info shared-libs
```

**Environment Structure:**
```
myproject/
├── .simple/
│   ├── env/                    # Environment root
│   │   ├── bin/                # Executables
│   │   │   ├── activate        # Bash activation
│   │   │   ├── activate.fish   # Fish activation
│   │   │   └── simple          # Simple binary (symlink or copy)
│   │   ├── lib/                # Installed packages
│   │   │   ├── http-client@1.0.0/
│   │   │   └── json-parser@2.3.1/
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

# Packages are isolated from other environments
simple env deactivate
simple env activate other-project
simple pkg list
# Different packages listed
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

**Package Search Path:**
```toml
# env.toml
[environment]
name = "myproject"
simple_version = "0.5.0"

[packages]
search_path = [
  ".simple/env/lib",          # Local environment (highest priority)
  "~/.simple/shared/lib",     # Shared packages
  "/usr/local/simple/lib"     # Global packages (lowest priority)
]
```

**Import Resolution:**
```simple
# Code automatically uses environment packages
import http_client  # Resolves to .simple/env/lib/http-client@1.0.0

fn main():
    let client = http_client.new()
    let response = client.get("https://api.example.com")
    print(response.body)
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

[[package]]
name = "socket-utils"
version = "2.1.0"
source = "registry+https://packages.simple-lang.org"
checksum = "sha256:e5f6g7h8..."
dependencies = []
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

**Export/Import Environments:**
```bash
# Export environment specification
simple env export > environment.toml

# environment.toml
[environment]
name = "myproject"
simple_version = "0.5.0"

[packages]
http-client = "1.0.0"
json-parser = "2.3.1"
web-framework = "2.0.0"

# Import on another machine
simple env create myproject --from-file=environment.toml
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

**Multiple Environments:**
```bash
# Development environment (loose)
simple env create dev
simple env activate dev
simple pkg add web-framework@latest

# Production environment (strict)
simple env create prod --from-lock
simple run --env=prod --sandbox=strict app.spl

# Testing environment (isolated)
simple env create test
simple run --env=test --sandbox=testing test_suite.spl
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

## Part 3: Implementation

### Rust Dependencies

```toml
# Cargo.toml
[dependencies]
# Environment isolation
serde = { version = "1.0", features = ["derive"] }
toml = "0.8"                    # TOML parsing for env.toml, simple.lock
walkdir = "2.4"                 # Directory traversal
shellexpand = "3.1"             # Shell variable expansion (~, $HOME)

# Sandbox - Cross-platform
rlimit = "0.10"                 # Resource limits (cross-platform)

# Sandbox - Linux
[target.'cfg(target_os = "linux")'.dependencies]
nix = { version = "0.27", features = ["process", "sched", "resource", "mount"] }
seccompiler = "0.4"             # Seccomp filter builder (Firecracker)
caps = "0.5"                    # Linux capabilities

# Sandbox - Windows
[target.'cfg(windows)'.dependencies]
windows = { version = "0.52", features = [
    "Win32_System_JobObjects",
    "Win32_System_Threading",
    "Win32_Security",
] }

# Sandbox - macOS
[target.'cfg(target_os = "macos")'.dependencies]
libc = "0.2"                    # For sandbox-exec spawn

# Docker backend
bollard = { version = "0.16", optional = true }  # Docker API client
tokio = { version = "1.35", features = ["full"], optional = true }

[features]
docker = ["bollard", "tokio"]   # Optional Docker backend
```

### Environment Isolation Implementation

**Environment Manager:**
```rust
// src/runtime/src/environment/mod.rs
use std::collections::HashMap;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::SystemTime;
use serde::{Deserialize, Serialize};
use anyhow::{Context, Result};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnvironmentConfig {
    pub name: String,
    pub simple_version: String,
    #[serde(with = "humantime_serde")]
    pub created: SystemTime,
    pub search_path: Vec<PathBuf>,
}

impl EnvironmentConfig {
    pub fn save(&self, path: impl AsRef<Path>) -> Result<()> {
        let toml = toml::to_string_pretty(self)?;
        fs::write(path, toml).context("Failed to write env.toml")
    }

    pub fn load(path: impl AsRef<Path>) -> Result<Self> {
        let content = fs::read_to_string(path)?;
        toml::from_str(&content).context("Failed to parse env.toml")
    }
}

pub struct Environment {
    name: String,
    root: PathBuf,
    simple_version: String,
    packages: HashMap<String, PackageInfo>,
    config: EnvironmentConfig,
}

impl Environment {
    pub fn create(name: &str, root: PathBuf) -> Result<Self> {
        // Create directory structure
        fs::create_dir_all(root.join("lib"))?;
        fs::create_dir_all(root.join("bin"))?;
        fs::create_dir_all(root.join("cache"))?;

        // Write activation scripts
        Self::write_activation_scripts(&root)?;

        // Expand home directory
        let home = shellexpand::tilde("~/.simple/shared/lib");

        // Create config
        let config = EnvironmentConfig {
            name: name.to_string(),
            created: SystemTime::now(),
            simple_version: env!("CARGO_PKG_VERSION").to_string(),
            search_path: vec![
                root.join("lib"),
                PathBuf::from(home.as_ref()),
            ],
        };
        config.save(root.join("env.toml"))?;

        Ok(Self {
            name: name.to_string(),
            root,
            simple_version: config.simple_version.clone(),
            packages: HashMap::new(),
            config,
        })
    }

    fn write_activation_scripts(root: &Path) -> Result<()> {
        let bin = root.join("bin");

        // Bash activation script
        let bash_script = format!(r#"#!/bin/bash
# Simple environment activation script
export SIMPLE_ENV="{name}"
export SIMPLE_ENV_ROOT="{root}"
export SIMPLE_PATH="{root}/lib:$SIMPLE_PATH"
export PS1="({name}) $PS1"

deactivate() {{
    export PS1="$_OLD_PS1"
    unset SIMPLE_ENV SIMPLE_ENV_ROOT
    unset -f deactivate
}}
"#, name = root.file_name().unwrap().to_str().unwrap(),
    root = root.display());

        fs::write(bin.join("activate"), bash_script)?;

        // Fish activation script
        let fish_script = format!(r#"#!/usr/bin/env fish
# Simple environment activation script for fish
set -gx SIMPLE_ENV "{name}"
set -gx SIMPLE_ENV_ROOT "{root}"
set -gx SIMPLE_PATH "{root}/lib" $SIMPLE_PATH

function deactivate
    set -e SIMPLE_ENV
    set -e SIMPLE_ENV_ROOT
    functions -e deactivate
end
"#, name = root.file_name().unwrap().to_str().unwrap(),
    root = root.display());

        fs::write(bin.join("activate.fish"), fish_script)?;

        Ok(())
    }

    pub fn activate(&self) -> Result<()> {
        // Set environment variables
        env::set_var("SIMPLE_ENV", &self.name);
        env::set_var("SIMPLE_ENV_ROOT", &self.root);

        // Prepend to package search path
        let mut path = self.root.join("lib").to_string_lossy().to_string();
        if let Ok(existing) = env::var("SIMPLE_PATH") {
            path.push(':');
            path.push_str(&existing);
        }
        env::set_var("SIMPLE_PATH", path);

        Ok(())
    }

    pub fn install_package(&mut self, pkg: &Package) -> Result<()> {
        let dest = self.root.join("lib").join(format!("{}@{}", pkg.name, pkg.version));
        pkg.install_to(&dest)?;
        self.packages.insert(pkg.name.clone(), pkg.info());
        self.update_lock_file()?;
        Ok(())
    }

    fn update_lock_file(&self) -> Result<()> {
        let lock = LockFile {
            version: 1,
            environment: self.config.clone(),
            packages: self.packages.clone(),
        };
        lock.save(self.root.join("simple.lock"))
    }
}

pub struct EnvironmentManager {
    active: Option<Environment>,
    environments: HashMap<String, PathBuf>,
}

impl EnvironmentManager {
    pub fn detect_environment() -> Option<PathBuf> {
        // Check environment variable
        if let Ok(root) = env::var("SIMPLE_ENV_ROOT") {
            return Some(PathBuf::from(root));
        }

        // Check for .simple/env/ in current directory or parents
        let mut dir = env::current_dir().ok()?;
        loop {
            let env_dir = dir.join(".simple/env");
            if env_dir.exists() && env_dir.join("env.toml").exists() {
                return Some(env_dir);
            }

            if !dir.pop() {
                break;
            }
        }

        None
    }

    pub fn load_environment(root: PathBuf) -> Result<Environment> {
        let config = EnvironmentConfig::load(root.join("env.toml"))?;
        let lock = LockFile::load(root.join("simple.lock"))?;

        Ok(Environment {
            name: config.name,
            root,
            simple_version: config.simple_version,
            packages: lock.packages,
            config,
        })
    }

    pub fn list_environments() -> Result<Vec<(String, PathBuf)>> {
        let mut envs = Vec::new();

        // Check global environments directory
        let global_dir = shellexpand::tilde("~/.simple/envs");
        if let Ok(entries) = fs::read_dir(global_dir.as_ref()) {
            for entry in entries.flatten() {
                if entry.path().join("env.toml").exists() {
                    let name = entry.file_name().to_string_lossy().to_string();
                    envs.push((name, entry.path()));
                }
            }
        }

        Ok(envs)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LockFile {
    pub version: u32,
    pub environment: EnvironmentConfig,
    pub packages: HashMap<String, PackageInfo>,
}

impl LockFile {
    pub fn save(&self, path: impl AsRef<Path>) -> Result<()> {
        let toml = toml::to_string_pretty(self)?;
        fs::write(path, toml).context("Failed to write simple.lock")
    }

    pub fn load(path: impl AsRef<Path>) -> Result<Self> {
        let content = fs::read_to_string(path)?;
        toml::from_str(&content).context("Failed to parse simple.lock")
    }
}
```

**Package Resolution with Environments:**
```rust
// src/pkg/src/resolver.rs
use walkdir::WalkDir;

impl PackageResolver {
    pub fn resolve_in_environment(&self, env: &Environment, name: &str) -> Result<PathBuf> {
        // Search in environment's package paths
        for search_path in &env.config.search_path {
            let candidates = self.find_packages_in_path(search_path, name)?;
            if let Some(pkg) = candidates.into_iter().max_by_key(|p| p.version) {
                return Ok(pkg.path);
            }
        }

        Err(PackageError::NotFound(name.to_string()))
    }

    fn find_packages_in_path(&self, search_path: &Path, name: &str) -> Result<Vec<PackageCandidate>> {
        let mut candidates = Vec::new();

        // Use walkdir for efficient directory traversal
        for entry in WalkDir::new(search_path)
            .max_depth(2)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            if entry.file_name().to_str().map(|s| s.starts_with(name)).unwrap_or(false) {
                if let Some(pkg) = self.parse_package(entry.path())? {
                    candidates.push(pkg);
                }
            }
        }

        Ok(candidates)
    }
}
```

### Runtime Sandboxing Implementation

### Strategy Selection

```rust
// src/runtime/src/sandbox/mod.rs
use anyhow::Result;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SandboxBackend {
    Native,     // OS-specific (namespaces, sandbox-exec, Job Objects)
    Docker,     // Docker containers
    None,       // No sandbox (development only)
}

impl SandboxBackend {
    pub fn auto_select() -> Self {
        if Self::can_use_native() {
            SandboxBackend::Native
        } else if cfg!(feature = "docker") && Self::docker_available() {
            SandboxBackend::Docker
        } else {
            eprintln!("Warning: No sandbox available, running without isolation");
            SandboxBackend::None
        }
    }

    fn can_use_native() -> bool {
        #[cfg(target_os = "linux")]
        {
            use nix::unistd::Uid;
            // Check if we can create user namespaces
            Uid::current().is_root() ||
                std::fs::read_to_string("/proc/sys/kernel/unprivileged_userns_clone")
                    .map(|s| s.trim() == "1")
                    .unwrap_or(false)
        }

        #[cfg(target_os = "macos")]
        {
            // sandbox-exec is always available on macOS
            true
        }

        #[cfg(target_os = "windows")]
        {
            // Job Objects available on all Windows versions
            true
        }

        #[cfg(not(any(target_os = "linux", target_os = "macos", target_os = "windows")))]
        {
            false
        }
    }

    fn docker_available() -> bool {
        #[cfg(feature = "docker")]
        {
            std::process::Command::new("docker")
                .arg("info")
                .output()
                .map(|o| o.status.success())
                .unwrap_or(false)
        }

        #[cfg(not(feature = "docker"))]
        {
            false
        }
    }
}

pub struct ResourceLimits {
    pub time_limit: Option<Duration>,
    pub memory_limit: Option<usize>,
    pub cpu_limit: Option<u32>,
    pub file_descriptors: Option<u64>,
}

pub struct Sandbox {
    backend: SandboxBackend,
    limits: ResourceLimits,
    network_allowed: bool,
    filesystem_allowed: Vec<PathBuf>,
}

impl Sandbox {
    pub fn new(backend: SandboxBackend, limits: ResourceLimits) -> Self {
        Self {
            backend,
            limits,
            network_allowed: false,
            filesystem_allowed: Vec::new(),
        }
    }

    pub fn run<F, R>(&self, f: F) -> Result<R>
    where
        F: FnOnce() -> Result<R>,
    {
        match self.backend {
            SandboxBackend::Native => {
                #[cfg(target_os = "linux")]
                return linux::run_sandboxed(f, &self.limits);

                #[cfg(target_os = "macos")]
                return macos::run_sandboxed(f, &self.limits);

                #[cfg(target_os = "windows")]
                return windows::run_sandboxed(f, &self.limits);

                #[cfg(not(any(target_os = "linux", target_os = "macos", target_os = "windows")))]
                anyhow::bail!("Native sandbox not supported on this platform");
            }

            SandboxBackend::Docker => {
                #[cfg(feature = "docker")]
                return docker::run_sandboxed(f, &self.limits);

                #[cfg(not(feature = "docker"))]
                anyhow::bail!("Docker backend not enabled (compile with --features docker)");
            }

            SandboxBackend::None => f(),
        }
    }
}
```

### Linux Implementation (Native)

**Using `nix` + `seccompiler` crates:**

```rust
// src/runtime/src/sandbox/linux.rs
use anyhow::{Context, Result};
use nix::sched::{unshare, CloneFlags};
use nix::sys::resource::{setrlimit, Resource, RLIM_INFINITY};
use nix::sys::wait::waitpid;
use nix::unistd::{fork, ForkResult};
use seccompiler::{
    BpfProgram, SeccompAction, SeccompCmpOp, SeccompCondition, SeccompFilter, SeccompRule,
};
use std::time::{Duration, Instant};
use super::ResourceLimits;

pub fn run_sandboxed<F, R>(f: F, limits: &ResourceLimits) -> Result<R>
where
    F: FnOnce() -> Result<R>,
{
    // Fork process for isolation
    match unsafe { fork()? } {
        ForkResult::Parent { child } => {
            // Wait for child and get result
            let status = waitpid(child, None)?;
            // TODO: Communicate result back from child
            todo!("IPC for result communication")
        }

        ForkResult::Child => {
            // In child process - set up sandbox
            setup_namespaces()?;
            apply_resource_limits(limits)?;
            apply_seccomp_filter()?;

            // Run the function
            let result = f();

            // Exit child process
            std::process::exit(result.is_ok() as i32);
        }
    }
}

fn setup_namespaces() -> Result<()> {
    // Create new namespaces for isolation
    unshare(
        CloneFlags::CLONE_NEWNET |  // Network namespace
        CloneFlags::CLONE_NEWPID |  // PID namespace
        CloneFlags::CLONE_NEWNS |   // Mount namespace
        CloneFlags::CLONE_NEWIPC |  // IPC namespace
        CloneFlags::CLONE_NEWUTS    // UTS namespace (hostname)
    ).context("Failed to create namespaces")?;

    Ok(())
}

fn apply_resource_limits(limits: &ResourceLimits) -> Result<()> {
    // CPU time limit
    if let Some(time_limit) = limits.time_limit {
        let secs = time_limit.as_secs();
        setrlimit(Resource::RLIMIT_CPU, secs, secs)
            .context("Failed to set CPU time limit")?;
    }

    // Memory limit (address space)
    if let Some(memory_limit) = limits.memory_limit {
        setrlimit(Resource::RLIMIT_AS, memory_limit as u64, memory_limit as u64)
            .context("Failed to set memory limit")?;
    }

    // File descriptor limit
    if let Some(fd_limit) = limits.file_descriptors {
        setrlimit(Resource::RLIMIT_NOFILE, fd_limit, fd_limit)
            .context("Failed to set file descriptor limit")?;
    } else {
        // Default to 100 file descriptors
        setrlimit(Resource::RLIMIT_NOFILE, 100, 100)?;
    }

    // Process limit (prevent fork bombs)
    setrlimit(Resource::RLIMIT_NPROC, 1, 1)
        .context("Failed to set process limit")?;

    Ok(())
}

fn apply_seccomp_filter() -> Result<()> {
    // Build seccomp filter using seccompiler
    let mut filter = SeccompFilter::new(
        vec![
            // Allow basic syscalls
            ("read", vec![]),
            ("write", vec![]),
            ("open", vec![]),
            ("openat", vec![]),
            ("close", vec![]),
            ("stat", vec![]),
            ("fstat", vec![]),
            ("lstat", vec![]),
            ("poll", vec![]),
            ("lseek", vec![]),
            ("mmap", vec![]),
            ("mprotect", vec![]),
            ("munmap", vec![]),
            ("brk", vec![]),
            ("rt_sigaction", vec![]),
            ("rt_sigprocmask", vec![]),
            ("rt_sigreturn", vec![]),
            ("ioctl", vec![]),
            ("readv", vec![]),
            ("writev", vec![]),
            ("access", vec![]),
            ("pipe", vec![]),
            ("select", vec![]),
            ("sched_yield", vec![]),
            ("mremap", vec![]),
            ("msync", vec![]),
            ("mincore", vec![]),
            ("madvise", vec![]),
            ("dup", vec![]),
            ("dup2", vec![]),
            ("getpid", vec![]),
            ("getppid", vec![]),
            ("getuid", vec![]),
            ("geteuid", vec![]),
            ("getgid", vec![]),
            ("getegid", vec![]),
            ("gettid", vec![]),
            ("sysinfo", vec![]),
            ("futex", vec![]),
            ("getcwd", vec![]),
            ("getdents", vec![]),
            ("getdents64", vec![]),
            ("fcntl", vec![]),
            ("flock", vec![]),
            ("fsync", vec![]),
            ("fdatasync", vec![]),
            ("truncate", vec![]),
            ("ftruncate", vec![]),
            ("chdir", vec![]),
            ("fchdir", vec![]),
            ("rename", vec![]),
            ("mkdir", vec![]),
            ("rmdir", vec![]),
            ("unlink", vec![]),
            ("link", vec![]),
            ("symlink", vec![]),
            ("readlink", vec![]),
            ("chmod", vec![]),
            ("fchmod", vec![]),
            ("chown", vec![]),
            ("fchown", vec![]),
            ("umask", vec![]),
            ("gettimeofday", vec![]),
            ("getrlimit", vec![]),
            ("getrusage", vec![]),
            ("times", vec![]),
            ("time", vec![]),
            ("getrandom", vec![]),
            ("exit_group", vec![]),
            ("exit", vec![]),

            // Deny network syscalls
            // ("socket", vec![]), // Commented = denied
            // ("bind", vec![]),
            // ("connect", vec![]),
            // ("accept", vec![]),
            // ("sendto", vec![]),
            // ("recvfrom", vec![]),
        ].into_iter()
            .map(|(name, rules)| (name.to_string(), rules))
            .collect(),
        SeccompAction::Errno(libc::EPERM as u32), // Default: deny
    ).context("Failed to create seccomp filter")?;

    // Apply the filter
    filter.apply().context("Failed to apply seccomp filter")?;

    Ok(())
}

```

### macOS Implementation

**Using `sandbox-exec` system command:**

```rust
// src/runtime/src/sandbox/macos.rs
use anyhow::{Context, Result};
use std::process::{Command, Stdio};
use std::time::Duration;
use super::ResourceLimits;

pub fn run_sandboxed<F, R>(f: F, limits: &ResourceLimits) -> Result<R>
where
    F: FnOnce() -> Result<R> + Send + 'static,
    R: Send + 'static,
{
    // Build sandbox profile
    let profile = build_sandbox_profile(limits)?;

    // Write profile to temp file
    let profile_path = std::env::temp_dir().join("simple_sandbox.sb");
    std::fs::write(&profile_path, profile)?;

    // Fork and run in child with sandbox-exec
    // Note: This is simplified - real implementation needs IPC
    let child = Command::new("sandbox-exec")
        .arg("-f")
        .arg(&profile_path)
        .arg(std::env::current_exe()?)
        .arg("--sandbox-child")  // Custom flag to run child code
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .context("Failed to spawn sandbox-exec")?;

    let output = child.wait_with_output()?;

    // Clean up profile file
    std::fs::remove_file(profile_path).ok();

    // TODO: Deserialize result from child output
    todo!("IPC for result communication")
}

fn build_sandbox_profile(limits: &ResourceLimits) -> Result<String> {
    let mut profile = String::from(r#"
(version 1)
(deny default)

;; Allow basic file operations
(allow file-read*
    (subpath "/usr/lib")
    (subpath "/usr/share")
    (subpath "/System")
    (subpath "/Library")
)

(allow file-write*
    (subpath "/tmp")
    (subpath "/var/tmp")
)

;; Allow process operations
(allow process-exec
    (literal (param "executable_path"))
)

(allow process-fork)
(allow signal)

;; Allow memory operations
(allow mach-lookup)
(allow mach-register)

;; Allow sysctl reads
(allow sysctl-read)

;; Deny network (unless explicitly allowed)
(deny network*)
(deny file-read* (subpath "/etc"))
(deny file-read* (subpath "/private/etc"))
"#);

    // Add resource-specific rules
    if let Some(memory_limit) = limits.memory_limit {
        // Note: sandbox-exec doesn't directly support memory limits
        // Would need to use setrlimit separately
    }

    profile.push_str(")\n");  // Close the profile

    Ok(profile)
}

// Alternative: Use rlimit directly without sandbox-exec
pub fn apply_resource_limits_macos(limits: &ResourceLimits) -> Result<()> {
    use libc::{setrlimit, rlimit, RLIMIT_CPU, RLIMIT_AS, RLIMIT_NOFILE};

    unsafe {
        // CPU time limit
        if let Some(time_limit) = limits.time_limit {
            let rlim = rlimit {
                rlim_cur: time_limit.as_secs(),
                rlim_max: time_limit.as_secs(),
            };
            if setrlimit(RLIMIT_CPU, &rlim) != 0 {
                return Err(anyhow::anyhow!("Failed to set CPU limit"));
            }
        }

        // Memory limit
        if let Some(memory_limit) = limits.memory_limit {
            let rlim = rlimit {
                rlim_cur: memory_limit as u64,
                rlim_max: memory_limit as u64,
            };
            if setrlimit(RLIMIT_AS, &rlim) != 0 {
                return Err(anyhow::anyhow!("Failed to set memory limit"));
            }
        }

        // File descriptor limit
        let fd_limit = limits.file_descriptors.unwrap_or(100);
        let rlim = rlimit {
            rlim_cur: fd_limit,
            rlim_max: fd_limit,
        };
        if setrlimit(RLIMIT_NOFILE, &rlim) != 0 {
            return Err(anyhow::anyhow!("Failed to set FD limit"));
        }
    }

    Ok(())
}
```

### Windows Implementation

**Using `windows` crate for Job Objects:**

```rust
// src/runtime/src/sandbox/windows.rs
use anyhow::{Context, Result};
use std::time::Duration;
use super::ResourceLimits;
use windows::{
    core::*,
    Win32::System::JobObjects::*,
    Win32::System::Threading::*,
    Win32::Foundation::*,
};

pub fn run_sandboxed<F, R>(f: F, limits: &ResourceLimits) -> Result<R>
where
    F: FnOnce() -> Result<R>,
{
    unsafe {
        // Create job object
        let job = CreateJobObjectW(None, None)
            .context("Failed to create job object")?;

        // Set resource limits
        apply_job_limits(job, limits)?;

        // Assign current process to job
        let current_process = GetCurrentProcess();
        AssignProcessToJobObject(job, current_process)
            .context("Failed to assign process to job")?;

        // Run the function
        let result = f();

        // Clean up (job object closes when handle is dropped)
        CloseHandle(job);

        result
    }
}

unsafe fn apply_job_limits(job: HANDLE, limits: &ResourceLimits) -> Result<()> {
    // Extended limit information
    let mut extended_limits: JOBOBJECT_EXTENDED_LIMIT_INFORMATION = std::mem::zeroed();

    // CPU time limit (in 100-nanosecond intervals)
    if let Some(time_limit) = limits.time_limit {
        let time_100ns = time_limit.as_nanos() / 100;
        extended_limits.BasicLimitInformation.PerProcessUserTimeLimit =
            time_100ns as i64;
        extended_limits.BasicLimitInformation.LimitFlags |=
            JOB_OBJECT_LIMIT_PROCESS_TIME;
    }

    // Memory limit
    if let Some(memory_limit) = limits.memory_limit {
        extended_limits.JobMemoryLimit = memory_limit;
        extended_limits.BasicLimitInformation.LimitFlags |=
            JOB_OBJECT_LIMIT_JOB_MEMORY;
    }

    // Process limit (prevent fork bombs)
    extended_limits.BasicLimitInformation.ActiveProcessLimit = 1;
    extended_limits.BasicLimitInformation.LimitFlags |=
        JOB_OBJECT_LIMIT_ACTIVE_PROCESS;

    // Kill processes when job closes
    extended_limits.BasicLimitInformation.LimitFlags |=
        JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE;

    // Apply the limits
    SetInformationJobObject(
        job,
        JobObjectExtendedLimitInformation,
        &extended_limits as *const _ as *const _,
        std::mem::size_of::<JOBOBJECT_EXTENDED_LIMIT_INFORMATION>() as u32,
    ).context("Failed to set job object limits")?;

    // UI restrictions (prevent creating windows, accessing clipboard, etc.)
    let mut ui_restrictions: JOBOBJECT_BASIC_UI_RESTRICTIONS = std::mem::zeroed();
    ui_restrictions.UIRestrictionsClass =
        JOB_OBJECT_UILIMIT_DESKTOP |
        JOB_OBJECT_UILIMIT_DISPLAYSETTINGS |
        JOB_OBJECT_UILIMIT_EXITWINDOWS |
        JOB_OBJECT_UILIMIT_GLOBALATOMS |
        JOB_OBJECT_UILIMIT_HANDLES |
        JOB_OBJECT_UILIMIT_READCLIPBOARD |
        JOB_OBJECT_UILIMIT_SYSTEMPARAMETERS |
        JOB_OBJECT_UILIMIT_WRITECLIPBOARD;

    SetInformationJobObject(
        job,
        JobObjectBasicUIRestrictions,
        &ui_restrictions as *const _ as *const _,
        std::mem::size_of::<JOBOBJECT_BASIC_UI_RESTRICTIONS>() as u32,
    ).context("Failed to set UI restrictions")?;

    Ok(())
}
```

### Docker Implementation

**Using `bollard` crate (Docker API client):**

```rust
// src/runtime/src/sandbox/docker.rs
#[cfg(feature = "docker")]
use anyhow::{Context, Result};
use bollard::container::{Config, CreateContainerOptions, RemoveContainerOptions};
use bollard::exec::{CreateExecOptions, StartExecResults};
use bollard::Docker;
use futures::StreamExt;
use std::default::Default;
use std::time::Duration;
use super::ResourceLimits;

#[cfg(feature = "docker")]
pub async fn run_sandboxed<F, R>(f: F, limits: &ResourceLimits) -> Result<R>
where
    F: FnOnce() -> Result<R> + Send + 'static,
    R: Send + 'static,
{
    // Connect to Docker daemon
    let docker = Docker::connect_with_local_defaults()
        .context("Failed to connect to Docker daemon")?;

    // Create container config
    let config = build_container_config(limits)?;

    // Create container
    let container_name = format!("simple-sandbox-{}", uuid::Uuid::new_v4());
    let container = docker
        .create_container(
            Some(CreateContainerOptions {
                name: &container_name,
                ..Default::default()
            }),
            config,
        )
        .await
        .context("Failed to create container")?;

    // Start container
    docker
        .start_container::<String>(&container.id, None)
        .await
        .context("Failed to start container")?;

    // Execute code in container
    // Note: This is simplified - real implementation needs to serialize function
    let exec = docker
        .create_exec(
            &container.id,
            CreateExecOptions {
                cmd: Some(vec!["/usr/bin/simple", "run", "/sandbox/code.spl"]),
                attach_stdout: Some(true),
                attach_stderr: Some(true),
                ..Default::default()
            },
        )
        .await
        .context("Failed to create exec")?;

    // Start execution and collect output
    let mut output = Vec::new();
    if let StartExecResults::Attached { mut output: stream, .. } =
        docker.start_exec(&exec.id, None).await?
    {
        while let Some(Ok(msg)) = stream.next().await {
            output.extend_from_slice(&msg.into_bytes());
        }
    }

    // Wait for container to finish
    let wait_result = docker
        .wait_container::<String>(&container.id, None)
        .next()
        .await
        .context("Failed to wait for container")??;

    // Clean up container
    docker
        .remove_container(
            &container.id,
            Some(RemoveContainerOptions {
                force: true,
                ..Default::default()
            }),
        )
        .await
        .ok();

    // TODO: Deserialize result from output
    todo!("Result deserialization from container output")
}

#[cfg(feature = "docker")]
fn build_container_config(limits: &ResourceLimits) -> Result<Config<String>> {
    use bollard::models::*;

    let mut host_config = HostConfig {
        // Memory limit (in bytes)
        memory: limits.memory_limit.map(|m| m as i64),

        // CPU quota (100000 = 100% of one core)
        cpu_quota: limits.cpu_limit.map(|c| (c as i64) * 1000),
        cpu_period: Some(100000),

        // Network mode
        network_mode: Some("none".to_string()),  // No network

        // Read-only root filesystem
        read_only_root_fs: Some(true),

        // Temp filesystem for /tmp
        tmpfs: Some(vec![("/tmp".to_string(), "".to_string())].into_iter().collect()),

        // No privileges
        privileged: Some(false),
        cap_drop: Some(vec!["ALL".to_string()]),

        ..Default::default()
    };

    Ok(Config {
        image: Some("simple-runtime:latest"),
        host_config: Some(host_config),
        network_disabled: Some(true),
        ..Default::default()
    })
}

// Synchronous wrapper for async Docker API
#[cfg(feature = "docker")]
pub fn run_sandboxed_sync<F, R>(f: F, limits: &ResourceLimits) -> Result<R>
where
    F: FnOnce() -> Result<R> + Send + 'static,
    R: Send + 'static,
{
    // Create Tokio runtime for async Docker API
    let runtime = tokio::runtime::Runtime::new()
        .context("Failed to create Tokio runtime")?;

    runtime.block_on(run_sandboxed(f, limits))
}
```

---

## Library Usage Summary

| Platform | Libraries Used | Purpose |
|----------|---------------|---------|
| **All** | `serde`, `toml` | Configuration serialization |
| **All** | `anyhow` | Error handling |
| **All** | `walkdir` | Directory traversal (package search) |
| **All** | `shellexpand` | Path expansion (~, $HOME) |
| **All** | `rlimit` | Cross-platform resource limits |
| **Linux** | `nix` 0.27 | Namespaces, setrlimit, fork/wait |
| **Linux** | `seccompiler` 0.4 | Seccomp filter (from Firecracker) |
| **Linux** | `caps` 0.5 | Linux capabilities |
| **macOS** | `libc` | setrlimit, system calls |
| **Windows** | `windows` 0.52 | Job Objects API |
| **Docker** | `bollard` 0.16 | Docker daemon API client |
| **Docker** | `tokio` 1.35 | Async runtime for bollard |

### Why These Libraries?

1. **nix** - Safe Rust wrappers for POSIX APIs, well-maintained, idiomatic
2. **seccompiler** - Production-tested (used by Firecracker VMM), handles complex filter rules
3. **windows** - Official Microsoft Rust bindings, modern and safe
4. **bollard** - Most mature Docker API client for Rust, async-first
5. **walkdir** - Fast directory traversal, handles symlinks correctly
6. **shellexpand** - Proper shell variable expansion (security-conscious)

### Performance Comparison

```
Backend         Launch   Runtime   Memory    Use Case
────────────────────────────────────────────────────────
Native (Linux)  5-20ms   1-3%      1-10MB    Default, REPL, tests
Native (macOS)  10-30ms  2-4%      2-15MB    Default on Mac
Native (Windows) 8-25ms  2-5%      2-12MB    Default on Windows
Docker          200ms-3s  5-10%    100-500MB CI/CD, max isolation
```

### Build Configuration

```toml
# Enable Docker backend (optional)
cargo build --features docker

# Default build (native sandbox only)
cargo build
```

This provides maximum performance using native OS primitives by default, with optional Docker backend for maximum isolation or CI/CD consistency.

---

## Benefits for LLM Tools

### Environment Isolation Benefits:
1. **No Dependency Conflicts** - Each project has its own packages
2. **Reproducible Builds** - Lock files ensure consistency across machines
3. **Easy Onboarding** - `simple env create --from-lock` sets up everything
4. **Clean Development** - No global package pollution
5. **Version Testing** - Multiple environments with different package versions

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

## Implementation Plan

### Part A: Environment Isolation (5 days)

**Phase 1: Environment Management (2 days)**
- [ ] Environment creation/deletion
- [ ] Activation scripts (bash, fish, zsh)
- [ ] Auto-detection from `.simple/env/` and `simple.toml`
- [ ] Environment listing and info commands
- [ ] Tests for environment lifecycle

**Phase 2: Package Isolation (2 days)**
- [ ] Per-environment package installation
- [ ] Package search path implementation
- [ ] Dependency resolution in environments
- [ ] Integration with existing package manager
- [ ] Tests for package isolation

**Phase 3: Reproducibility (1 day)**
- [ ] Lock file generation/parsing
- [ ] Environment export/import
- [ ] Verification against lock files
- [ ] Sync command implementation
- [ ] Tests for reproducibility

### Part B: Runtime Sandboxing (7 days)

**Phase 4: Resource Limits (2 days)**
- [ ] Time limit enforcement
- [ ] Memory limit enforcement
- [ ] CPU usage limits
- [ ] Tests for limits

**Phase 5: Network Isolation (2 days)**
- [ ] Block all network by default
- [ ] Allowlist implementation
- [ ] Domain filtering
- [ ] Tests for network isolation

**Phase 6: Filesystem Isolation (2 days)**
- [ ] Block all filesystem by default
- [ ] Allow specific directories
- [ ] Virtual filesystem overlay
- [ ] Tests for filesystem isolation

**Phase 7: CLI Integration (1 day)**
- [ ] `--sandbox` flag
- [ ] Profile system
- [ ] Configuration file support
- [ ] Documentation

### Part C: Integration (2 days)

**Phase 8: Environment + Sandbox (2 days)**
- [ ] Combined `--env` and `--sandbox` flags
- [ ] Environment-specific sandbox profiles
- [ ] Test framework integration
- [ ] CI/CD workflow examples
- [ ] Complete documentation
- [ ] End-to-end tests

**Total Estimated Effort:** 14 days (5 env + 7 sandbox + 2 integration)

## File Structure

```
src/runtime/src/
├── environment/        # Environment isolation (virtualenv-style)
│   ├── mod.rs          # Environment manager
│   ├── config.rs       # Environment configuration (env.toml)
│   ├── lock.rs         # Lock file handling (simple.lock)
│   ├── activation.rs   # Shell activation scripts
│   └── detection.rs    # Auto-detection logic
│
├── sandbox/            # Runtime sandboxing (container-style)
│   ├── mod.rs          # Main sandbox API
│   ├── linux.rs        # Linux implementation (seccomp)
│   ├── macos.rs        # macOS implementation (sandbox-exec)
│   ├── windows.rs      # Windows implementation (job objects)
│   ├── limits.rs       # Resource limits
│   ├── network.rs      # Network filtering
│   └── filesystem.rs   # Filesystem restrictions
│
└── isolation/          # Integration layer
    ├── mod.rs          # Combined environment + sandbox
    └── profiles.rs     # Sandbox profiles per environment

src/pkg/src/
├── environment.rs      # Package installation in environments
└── resolver.rs         # Package resolution with environments

src/driver/src/
├── env_commands.rs     # CLI: env create/activate/list/info
└── sandbox_runner.rs   # Runner with sandbox integration

tests/
├── environment/
│   ├── creation_spec.rs        # Environment lifecycle tests
│   ├── package_isolation_spec.rs  # Package isolation tests
│   └── reproducibility_spec.rs    # Lock file tests
│
├── sandbox/
│   ├── limits_spec.rs      # Resource limit tests
│   ├── network_spec.rs     # Network isolation tests
│   └── filesystem_spec.rs  # Filesystem isolation tests
│
└── integration/
    └── env_sandbox_spec.rs # Combined environment + sandbox tests
```

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

## Success Metrics

### Environment Isolation (#920-923):
- [ ] Zero dependency conflicts across projects
- [ ] 100% reproducible builds from lock files
- [ ] <100ms environment activation time
- [ ] Supports all major shells (bash, zsh, fish)
- [ ] Package resolution <50ms overhead
- [ ] 90%+ developer satisfaction (virtualenv parity)

### Runtime Sandboxing (#916-919):
- [ ] 100% of malicious code contained
- [ ] Zero false positives (legitimate code runs)
- [ ] <5% performance overhead
- [ ] Works on Linux, macOS, Windows
- [ ] Network isolation 100% effective
- [ ] Filesystem restrictions enforceable
- [ ] 95%+ developer satisfaction (container parity)

### Combined System (#916-923):
- [ ] Environment + sandbox work seamlessly together
- [ ] CI/CD workflows use both features
- [ ] LLM-generated code runs safely in isolated environments
- [ ] Documentation covers all use cases
- [ ] Zero security incidents in production

## References

**Environment Isolation (virtualenv-style):**
- **Python venv** - Virtual environment model
- **Node.js npm** - Local node_modules pattern
- **Rust Cargo** - Cargo.lock reproducibility
- **UV** - Fast Python package manager

**Runtime Sandboxing (container-style):**
- **Docker** - Container isolation
- **Firejail** - Linux sandbox
- **systemd-run** - Resource limits
- **seccomp** - Syscall filtering
- **bubblewrap** - Unprivileged sandboxing

**Combined Approaches:**
- **Nix** - Reproducible builds with isolation
- **Bazel** - Hermetic build environments
- **Podman** - Rootless containers

---

## Next Steps

### Phase 1: Environment Isolation (Weeks 1-2)
1. Design environment manager API
2. Implement environment creation/activation
3. Add package isolation to package manager
4. Create lock file format and sync
5. Write comprehensive tests
6. Document CLI commands and workflows

### Phase 2: Runtime Sandboxing (Weeks 3-4)
1. Review and approve sandbox specification
2. Implement Linux version first (seccomp + namespaces)
3. Add macOS support (sandbox-exec)
4. Add Windows support (job objects)
5. Test with LLM-generated code
6. Document security model

### Phase 3: Integration (Week 5)
1. Integrate environment + sandbox systems
2. Add combined CLI flags (`--env` + `--sandbox`)
3. Create profile system for different use cases
4. CI/CD workflow examples
5. End-to-end testing
6. Final documentation

### Completion Criteria:
- [ ] Mark #920-923 complete (environment isolation)
- [ ] Mark #916-919 complete (runtime sandboxing)
- [ ] All tests passing (100% coverage)
- [ ] Documentation complete with examples
- [ ] Works on Linux, macOS, Windows
- [ ] Production-ready for LLM tools

---

## Summary

This specification covers **8 features (#916-923)** providing complete isolation for Simple projects:

### Environment Isolation (Virtualenv-Style) - #920-923
**Like Python's venv:** Dependency isolation, project-local packages, reproducible builds
- #920: Environment creation & management
- #921: Package isolation
- #922: Environment reproducibility (lock files)
- #923: Environment + sandbox integration

### Runtime Sandboxing (Container-Style) - #916-919
**Like Docker:** Process isolation, resource limits, security restrictions
- #916: Resource limits (CPU, memory, time)
- #917: Network isolation (block/allowlist)
- #918: Filesystem isolation (read/write restrictions)
- #919: `simple run --sandbox` CLI

### Key Workflows

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

This provides the **best of both worlds**: dependency isolation (like Python venv) + runtime security (like containers), making Simple ideal for LLM-assisted development with safe execution of generated code.
