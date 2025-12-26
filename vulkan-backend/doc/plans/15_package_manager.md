# Package Manager Design

UV-style fast package management for Simple language.

## Overview

A package manager that is:
- **Fast** - Parallel downloads, global cache, incremental resolution
- **Flexible** - Git registry (free) or server registry (scalable)
- **Simple** - Minimal configuration, sensible defaults

## Why UV is Fast

UV (Python's fast package installer) achieves 10-100x speedup through:

### 1. Rust Implementation
- Zero-cost abstractions, no GC pauses
- Memory-safe parallelism with Rayon
- Efficient string handling (no Python object overhead)

### 2. PubGrub Resolution Algorithm
- Modern SAT-solver based dependency resolution
- Backtracking with conflict-driven clause learning
- Much faster than pip's backtracking resolver

### 3. Parallel Operations
```
Traditional:          UV-style:
fetch A               fetch A ─┬─ fetch B
  ↓                            ├─ fetch C
fetch B                        └─ fetch D
  ↓                   (parallel HTTP/2 multiplexing)
fetch C
  ↓
fetch D
```

### 4. Global Cache with Hard Links
```
~/.simple/cache/
├── packages/
│   └── http-1.0.0/        # Downloaded once
└── git/
    └── abc123.../         # Git repos cached

project-a/deps/http -> hard link to cache
project-b/deps/http -> hard link to cache (no copy!)
```

### 5. Lazy Metadata Fetching
- Only fetch metadata for packages actually needed
- Stop resolution early on conflicts
- Stream package index incrementally

### 6. HTTP/2 Multiplexing
- Single TCP connection for multiple requests
- Header compression (HPACK)
- Server push for predictable requests

### 7. Memory-Mapped I/O
- Large files read via mmap (no buffer copies)
- OS handles caching automatically

## Registry Design

### Phase 1: Git Registry (No Server)

A GitHub repository serves as the package index:

```
simple-registry/                    # https://github.com/simple-lang/registry
├── config.toml                     # Registry metadata
├── index/
│   ├── 1/                          # Single-char package names
│   │   └── a/
│   │       └── a.toml
│   ├── 2/                          # Two-char names
│   │   └── ab/
│   │       └── ab.toml
│   ├── 3/                          # Three-char names
│   │   └── abc/
│   │       └── abc.toml
│   └── ht/                         # First 2 chars as directory
│       └── tp/                     # Next 2 chars
│           └── http.toml           # Package manifest
└── README.md
```

#### Registry Config (config.toml)
```toml
[registry]
name = "simple-registry"
version = 1
api_version = "0.1"

[download]
# Where packages are actually hosted
default = "github"  # Packages hosted on GitHub

[urls]
# Template for package downloads
github = "https://github.com/{owner}/{repo}/archive/refs/tags/{tag}.tar.gz"
```

#### Package Index Entry (index/ht/tp/http.toml)
```toml
[package]
name = "http"
description = "HTTP client library for Simple"
repository = "https://github.com/simple-lang/http"
documentation = "https://simple-lang.org/docs/http"
keywords = ["http", "web", "client", "networking"]
license = "MIT"
owners = ["alice", "bob"]

# Version entries (append-only, newest last)
[[versions]]
version = "1.0.0"
published = "2024-12-01T00:00:00Z"
yanked = false
checksum = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
deps = []

[[versions]]
version = "1.1.0"
published = "2024-12-15T00:00:00Z"
yanked = false
checksum = "sha256:abc123..."
deps = [
    { name = "url", version = ">=1.0" },
    { name = "tls", version = "^2.0", optional = true }
]

[[versions]]
version = "1.0.1"  # Patch release (order by publish date, not version)
published = "2024-12-10T00:00:00Z"
yanked = false
checksum = "sha256:def456..."
deps = []
```

### Phase 2: Registry Server (Optional)

HTTP API for better performance and features:

```
GET  /api/v1/packages                    # List packages
GET  /api/v1/packages/{name}             # Package info
GET  /api/v1/packages/{name}/{version}   # Version info
GET  /api/v1/packages/{name}/versions    # All versions
POST /api/v1/packages                    # Publish (authenticated)
GET  /api/v1/search?q={query}            # Full-text search
GET  /api/v1/index/updates?since={hash}  # Incremental index updates
```

#### Server Benefits
- Full-text search
- Download statistics
- Instant publish (no PR review)
- Rate limiting / abuse prevention
- CDN distribution

## Project Manifest (simple.toml)

```toml
[package]
name = "myapp"
version = "0.1.0"
authors = ["Alice <alice@example.com>"]
description = "My awesome app"
license = "MIT"
repository = "https://github.com/alice/myapp"
keywords = ["cli", "tool"]

# Entry point
main = "src/main.spl"

[dependencies]
# Registry packages
http = "1.0"                              # Latest 1.x
json = "^2.1"                             # Compatible with 2.1
crypto = ">=1.0, <3.0"                    # Range

# Git dependencies
mylib = { git = "https://github.com/alice/mylib" }
private = { git = "git@github.com:corp/private.git", branch = "main" }
specific = { git = "https://github.com/bob/lib", tag = "v1.2.3" }
commit = { git = "https://github.com/bob/lib", rev = "abc1234" }

# Path dependencies (local development)
utils = { path = "../utils" }

# Optional dependencies
tls = { version = "2.0", optional = true }

[dev-dependencies]
# Only for tests/development
test-utils = "1.0"
benchmark = { git = "https://github.com/simple-lang/bench" }

[build-dependencies]
# For build scripts
codegen = "0.5"

[features]
default = ["json"]
full = ["http", "json", "crypto", "tls"]
minimal = []

[registry]
# Default registry (can be overridden)
default = "https://github.com/simple-lang/registry"
# Or server: default = "https://registry.simple-lang.org"
```

## Lock File (simple.lock)

```toml
# Auto-generated - do not edit
version = 1
generated = "2024-12-09T10:30:00Z"

[[package]]
name = "http"
version = "1.1.0"
source = "registry"
checksum = "sha256:abc123..."
dependencies = ["url 1.2.0"]

[[package]]
name = "url"
version = "1.2.0"
source = "registry"
checksum = "sha256:def456..."
dependencies = []

[[package]]
name = "mylib"
version = "0.5.0"
source = "git+https://github.com/alice/mylib#abc1234def5678"
dependencies = []

[[package]]
name = "utils"
version = "0.1.0"
source = "path+../utils"
dependencies = []
```

## CLI Commands

```bash
# Initialize new project
simple init                    # Create simple.toml
simple init --lib              # Create library project

# Dependency management
simple add http                # Add latest version
simple add http@1.0            # Add specific version
simple add http --git https://github.com/user/http
simple add ../mylib --path     # Add local path
simple remove http             # Remove dependency
simple update                  # Update all deps
simple update http             # Update specific dep

# Install and build
simple install                 # Install all dependencies
simple build                   # Build project
simple run                     # Build and run
simple test                    # Run tests

# Publishing (Phase 1: Git registry)
simple publish --dry-run       # Validate package
simple publish                 # Create PR to registry repo

# Publishing (Phase 2: Server)
simple login                   # Authenticate
simple publish                 # Upload to server

# Cache management
simple cache clean             # Clear cache
simple cache list              # Show cached packages

# Registry
simple search http             # Search packages
simple info http               # Show package details
```

## Directory Structure

### Global Cache
```
~/.simple/
├── config.toml                # Global config
├── credentials.toml           # Auth tokens (chmod 600)
├── cache/
│   ├── registry/
│   │   └── github.com-simple-lang-registry/
│   │       ├── config.toml
│   │       └── index/...      # Sparse checkout of index
│   ├── packages/
│   │   ├── http-1.0.0/
│   │   │   ├── src/
│   │   │   └── simple.toml
│   │   └── http-1.1.0/
│   └── git/
│       └── github.com-alice-mylib-abc1234/
└── bin/                       # Installed binaries
```

### Project Layout
```
myapp/
├── simple.toml                # Project manifest
├── simple.lock                # Lock file (committed)
├── src/
│   ├── main.spl               # Entry point
│   └── lib.spl                # Library code
├── tests/
│   └── test_main.spl
├── deps/                      # Dependencies (hard links to cache)
│   ├── http -> ~/.simple/cache/packages/http-1.1.0
│   └── mylib -> ~/.simple/cache/git/github.com-alice-mylib-abc1234
└── target/
    ├── debug/
    └── release/
```

## Implementation Architecture

```
src/pkg/                       # New package manager crate
├── lib.rs
├── manifest.rs                # simple.toml parsing
├── lock.rs                    # simple.lock handling
├── resolver/
│   ├── mod.rs
│   ├── pubgrub.rs             # PubGrub algorithm
│   └── version.rs             # SemVer handling
├── registry/
│   ├── mod.rs
│   ├── git.rs                 # Git registry client
│   └── server.rs              # HTTP registry client
├── cache/
│   ├── mod.rs
│   ├── global.rs              # Global cache management
│   └── hardlink.rs            # Hard link utilities
├── fetch/
│   ├── mod.rs
│   ├── git.rs                 # Git fetch
│   ├── http.rs                # HTTP/2 fetch
│   └── parallel.rs            # Parallel download manager
└── commands/
    ├── mod.rs
    ├── add.rs
    ├── install.rs
    ├── publish.rs
    └── search.rs
```

## Performance Targets

| Operation | Target | UV Reference |
|-----------|--------|--------------|
| Cold install (10 deps) | < 2s | ~1s |
| Warm install (cached) | < 100ms | ~50ms |
| Resolution (100 deps) | < 500ms | ~200ms |
| `simple add pkg` | < 1s | ~500ms |

## Implementation Phases

### Phase 1: Core (MVP)
- [ ] simple.toml parsing
- [ ] simple.lock generation
- [ ] Git dependencies (path, git URL)
- [ ] Basic resolution (no conflicts)
- [ ] Global cache with hard links
- [ ] `simple init`, `simple add`, `simple install`

### Phase 2: Git Registry
- [ ] Git registry client
- [ ] Sparse checkout (only fetch needed index files)
- [ ] `simple search`, `simple info`
- [ ] `simple publish` (PR-based)
- [ ] Version resolution with constraints

### Phase 3: Performance
- [ ] PubGrub resolver
- [ ] Parallel HTTP/2 downloads
- [ ] Incremental index updates
- [ ] Memory-mapped package extraction

### Phase 4: Server Registry (Optional)
- [ ] HTTP API client
- [ ] Token authentication
- [ ] `simple login`, `simple publish`
- [ ] Full-text search

## Dependencies (Rust Crates)

```toml
[dependencies]
# Manifest parsing
toml = "0.8"
serde = { version = "1", features = ["derive"] }

# Version handling
semver = "1"

# Resolution
pubgrub = "0.2"              # PubGrub algorithm

# Network
reqwest = { version = "0.11", features = ["http2", "stream"] }
tokio = { version = "1", features = ["full"] }

# Git
git2 = "0.18"                # libgit2 bindings

# Cache
directories = "5"            # Platform cache dirs
fs_extra = "1"               # Hard link, copy

# CLI
clap = { version = "4", features = ["derive"] }

# Hashing
sha2 = "0.10"
```

## Security Considerations

1. **Checksum Verification** - All packages verified against SHA256
2. **Lock File** - Reproducible builds with exact versions
3. **Credential Storage** - Tokens in `~/.simple/credentials.toml` (chmod 600)
4. **Git SSH** - Support SSH keys for private repos
5. **HTTPS Only** - No HTTP for registry communication
6. **Yanked Versions** - Warn but allow install of yanked packages

## References

- [UV Documentation](https://github.com/astral-sh/uv)
- [PubGrub Algorithm](https://nex3.medium.com/pubgrub-2fb6470504f)
- [Cargo Registry Protocol](https://doc.rust-lang.org/cargo/reference/registry-index.html)
- [Go Modules](https://go.dev/ref/mod)
