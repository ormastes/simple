# Environment Isolation (#920-923)

**Part of:** [Sandboxed Execution](sandboxed_execution.md)
**Status:** 📋 Planned
**Category:** LLM-Friendly Features

## Overview

Environment isolation provides **package and dependency isolation** per project, similar to Python virtualenv. This enables reproducible builds, eliminates dependency conflicts, and allows multiple projects with different package versions to coexist.

**Like Python virtualenv:**
- Isolate packages and dependencies per project
- Project-local package cache
- Reproducible dependency sets
- Fast activation/deactivation
- No process overhead

## Features

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

## See Also

- [Runtime Sandboxing](sandbox_runtime.md) - Process isolation and resource limits
- [Implementation Details](sandbox_implementation.md) - Technical implementation
- [Sandboxed Execution Overview](sandboxed_execution.md) - Complete specification
