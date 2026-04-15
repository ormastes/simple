# Simple Package Manager - Implementation Plan

**Date:** 2026-02-01
**Status:** Ready to Begin
**Based On:** Design document + research findings

---

## Overview

Implementation plan for Simple's package manager, prioritizing quick wins (global cache) before complex features (registry, advanced resolver).

**Target Timeline:** 10-14 weeks total
**Priority:** High (enables Simple ecosystem growth)

---

## Phase Summary

| Phase | Focus | Duration | Priority | Status |
|-------|-------|----------|----------|--------|
| 3.5 | Dependency Foundation | 2-3 weeks | **High** | ⏳ Ready to start |
| 4 | Global Cache | 1-2 weeks | **High** | Pending 3.5 |
| 5 | Git Registry | 2-3 weeks | Medium | Pending 4 |
| 6 | PubGrub Resolver | 3-4 weeks | Medium | Pending 5 |
| 7 | Parallel HTTP/2 | 1-2 weeks | Low | Pending 6 |
| 8 | HTTP Registry | 4-6 weeks | Low | Future |

---

## Phase 3.5: Dependency Foundation

**Duration:** 2-3 weeks
**Goal:** Basic dependency resolution with path + git deps

### Tasks

#### Week 1: Manifest & Lockfile

**Day 1-2: Manifest Parser**
- [ ] Create `src/app/package/manifest.spl` (enhance existing)
- [ ] Parse `dependencies` section
- [ ] Parse `dev_dependencies` section
- [ ] Support version constraints: `^1.0`, `>=1.0, <2.0`, `*`
- [ ] Support git dependencies: `{git: url, tag/branch/commit}`
- [ ] Support path dependencies: `{path: ../utils}`
- [ ] Write tests: `src/app/package/manifest_spec.spl`

**Files to modify:**
```
src/app/package/
├── manifest.spl          # Enhance with dependency parsing
├── manifest_spec.spl     # Tests
└── types.spl             # Add Dependency, Constraint types
```

**Example:**
```simple
# manifest.spl

struct Dependency:
    name: text
    constraint: VersionConstraint    # ^1.0, >=1.0, etc.
    source: DependencySource         # Registry, Git, Path

enum DependencySource:
    Registry
    Git(url: text, ref: GitRef)
    Path(path: text)

fn parse_manifest(path: text) -> Manifest:
    val sdn = rt_sdn_parse(path)
    val deps = sdn.get("dependencies")
    # Parse each dependency...
```

**Day 3-4: Lockfile Generator**
- [ ] Create `src/app/package/lockfile.spl`
- [ ] Define lockfile schema (SDN table format)
- [ ] Implement lockfile writer
- [ ] Implement lockfile reader
- [ ] Checksum calculation (SHA256 via FFI)
- [ ] Write tests: `src/app/package/lockfile_spec.spl`

**Lockfile Format:**
```sdn
lockfile_version: 1
generated: 2026-02-01T12:34:56Z

packages |name, version, source, checksum|
  http, 1.1.0, registry, sha256:abc123...
  utils, 0.1.0, path+../utils, sha256:def456...
```

**Day 5: SemVer Parser**
- [ ] Create `src/app/package/semver.spl`
- [ ] Parse version strings: `1.2.3`, `1.2.3-alpha.1`
- [ ] Parse constraints: `^1.0`, `~1.2.3`, `>=1.0, <2.0`
- [ ] Version comparison: `satisfies(version, constraint)`
- [ ] Write tests: `src/app/package/semver_spec.spl`

**Example:**
```simple
# semver.spl

struct Version:
    major: i64
    minor: i64
    patch: i64
    prerelease: text?

fn parse_version(s: text) -> Version:
    val parts = s.split(".")
    Version(major: parts[0].to_int(), ...)

fn satisfies(version: Version, constraint: Constraint) -> bool:
    match constraint:
        Caret(base): version.major == base.major and version >= base
        Tilde(base): version.minor == base.minor and version >= base
        Range(min, max): version >= min and version < max
```

#### Week 2: Dependency Resolver

**Day 1-3: Backtracking Resolver**
- [ ] Create `src/app/package/resolver.spl`
- [ ] Implement simple backtracking algorithm
- [ ] Build dependency graph
- [ ] Detect cycles
- [ ] Error messages for conflicts
- [ ] Write tests: `src/app/package/resolver_spec.spl`

**Algorithm:**
```simple
# resolver.spl

fn resolve(manifest: Manifest) -> ResolutionResult:
    var graph = DependencyGraph()
    var stack = [manifest.dependencies]

    while not stack.is_empty():
        val dep = stack.pop()

        # Try each compatible version (newest first)
        val versions = find_versions(dep.name, dep.constraint)
        for version in versions:
            if can_add_to_graph(graph, dep.name, version):
                graph.add(dep.name, version)
                stack.push(version.dependencies)
                break
            else:
                # Conflict - try next version
                continue

        if not added:
            return Err("Conflict: cannot satisfy {dep}")

    Ok(graph)
```

**Day 4-5: Integration**
- [ ] Update `src/app/package/install.spl` to use resolver
- [ ] Generate lockfile after resolution
- [ ] Read lockfile if exists (skip resolution)
- [ ] Write end-to-end test

#### Week 3: Path & Git Dependencies

**Day 1-2: Path Dependencies**
- [ ] Resolve relative paths
- [ ] Read manifest from path
- [ ] Calculate checksum of source files
- [ ] Copy to deps/ directory
- [ ] Write tests

**Example:**
```simple
# Install path dependency
fn install_path_dep(dep: PathDependency) -> Result:
    val source_path = resolve_path(dep.path)
    val manifest = parse_manifest(source_path + "/simple.sdn")

    # Calculate checksum of all source files
    val checksum = calculate_dir_checksum(source_path)

    # Copy to deps/
    rt_package_copy_dir(source_path, "./deps/" + dep.name)

    Ok(checksum)
```

**Day 3-5: Git Dependencies (Basic)**
- [ ] Use `git clone` via rt_process_run
- [ ] Checkout specific tag/branch/commit
- [ ] Read manifest from repo
- [ ] Calculate checksum of commit
- [ ] Copy to deps/ directory
- [ ] Write tests

**Example:**
```simple
# Install git dependency
fn install_git_dep(dep: GitDependency) -> Result:
    val temp_dir = "/tmp/simple-git-" + random_id()

    # Clone repository
    rt_process_run("git clone {dep.url} {temp_dir}")

    # Checkout ref
    match dep.ref:
        Tag(t): rt_process_run("git checkout tags/{t}")
        Branch(b): rt_process_run("git checkout {b}")
        Commit(c): rt_process_run("git checkout {c}")

    # Read manifest
    val manifest = parse_manifest(temp_dir + "/simple.sdn")

    # Get commit hash for checksum
    val commit = get_git_commit_hash(temp_dir)

    # Copy to deps/
    rt_package_copy_dir(temp_dir, "./deps/" + dep.name)

    # Cleanup
    rt_package_remove_dir_all(temp_dir)

    Ok("git+{dep.url}#{commit}")
```

### Deliverables

- [x] Manifest parser with dependency support
- [x] Lockfile generator/reader
- [x] SemVer parser and constraint matching
- [x] Backtracking dependency resolver
- [x] Path dependencies working
- [x] Git dependencies working (basic)
- [x] `simple install` uses resolver
- [x] `simple add <package>` updates manifest
- [x] Tests for all components

### Success Criteria

```bash
# Create project
simple init myapp
cd myapp

# Add path dependency
simple add --path ../utils

# Add git dependency
simple add mylib --git https://github.com/alice/mylib --tag v1.0.0

# Install creates lockfile
simple install
# → generates simple.lock
# → downloads deps to deps/

# Reinstall uses lockfile
rm -rf deps/
simple install
# → uses simple.lock (reproducible)
```

---

## Phase 4: Global Cache

**Duration:** 1-2 weeks
**Goal:** Global cache with hard links for 70% disk savings

### Tasks

#### Week 1: Cache Implementation

**Day 1-2: Cache Structure**
- [ ] Create `src/app/package/cache.spl`
- [ ] Initialize cache directory: `~/.simple/cache/packages/`
- [ ] Store packages by name-version: `http-1.1.0/`
- [ ] Add checksum verification
- [ ] Write tests

**Example:**
```simple
# cache.spl

struct Cache:
    root: text    # ~/.simple/cache

fn init_cache() -> Cache:
    val home = rt_env_home()
    val root = home + "/.simple/cache"
    rt_package_mkdir_all(root + "/packages")
    rt_package_mkdir_all(root + "/git")
    Cache(root: root)

fn cache_package(cache: Cache, pkg: Package, content: bytes) -> Result:
    val pkg_dir = cache.root + "/packages/" + pkg.name + "-" + pkg.version
    rt_package_mkdir_all(pkg_dir)

    # Extract package to cache
    extract_package(content, pkg_dir)

    # Verify checksum
    val actual = calculate_checksum(pkg_dir)
    if actual != pkg.checksum:
        return Err("Checksum mismatch")

    Ok(pkg_dir)
```

**Day 3-4: Hard Link Installer**
- [ ] Modify `src/app/package/install.spl`
- [ ] Check cache before downloading
- [ ] Create hard links from cache to deps/
- [ ] Fallback to copy on Windows (if hard link fails)
- [ ] Write tests

**Example:**
```simple
# install.spl

fn install_from_cache(cache: Cache, pkg: Package) -> Result:
    val cache_path = cache.root + "/packages/" + pkg.name + "-" + pkg.version
    val dest_path = "./deps/" + pkg.name

    if not rt_package_exists(cache_path):
        return Err("Not in cache")

    # Try hard link (fast)
    if rt_package_create_hardlink(cache_path, dest_path) == 0:
        return Ok("hard-link")

    # Fallback to copy (Windows without admin)
    if rt_package_copy_dir(cache_path, dest_path) == 0:
        return Ok("copy")

    Err("Failed to install from cache")
```

**Day 5: Cache Management**
- [ ] `simple cache info` - show cache stats
- [ ] `simple cache clean` - remove unused packages
- [ ] `simple cache clear` - delete all cached packages
- [ ] Write tests

**Example:**
```simple
# cache_commands.spl

fn cache_info(cache: Cache):
    val packages = list_cache_packages(cache)
    val total_size = packages.map(|p| p.size).sum()

    print "Cache directory: {cache.root}"
    print "Total size: {format_bytes(total_size)}"
    print "Packages: {packages.length}"

fn cache_clean(cache: Cache):
    # Find packages not referenced by any project
    val all_pkgs = list_cache_packages(cache)
    val used_pkgs = find_used_packages()

    for pkg in all_pkgs:
        if not used_pkgs.contains(pkg):
            rt_package_remove_dir_all(pkg.path)
            print "Removed {pkg.name}-{pkg.version}"
```

### Deliverables

- [x] Global cache directory created on first use
- [x] Packages stored in cache
- [x] Hard links created to deps/
- [x] Fallback to copy on Windows
- [x] Cache management commands
- [x] 70% disk savings measured

### Success Criteria

```bash
# First install (cold cache)
simple install
# → Downloads to cache
# → Creates hard links to deps/
# → Time: ~2s for 10 packages

# Second install (warm cache)
rm -rf deps/
simple install
# → Uses cache
# → Creates hard links
# → Time: ~50ms for 10 packages

# Cache stats
simple cache info
# Cache directory: ~/.simple/cache
# Total size: 50 MB
# Packages: 15
# Disk saved: 120 MB (70%)
```

---

## Phase 5: Git Registry

**Duration:** 2-3 weeks
**Goal:** Fetch packages from GitHub-based registry

### Tasks

#### Week 1: Registry Protocol

**Day 1-2: Sparse Index Client**
- [ ] Create `src/app/package/registry.spl`
- [ ] Implement sparse protocol (HTTP GET)
- [ ] Fetch package metadata from index
- [ ] Parse registry SDN format
- [ ] Write tests

**Example:**
```simple
# registry.spl

struct Registry:
    url: text    # https://github.com/simple-lang/registry/index/

fn fetch_package_metadata(registry: Registry, name: text) -> PackageMetadata:
    # Compute index path: http → ht/tp/http.sdn
    val path = name_to_index_path(name)
    val url = registry.url + "/" + path

    # Fetch via HTTP
    val response = rt_http_get(url)
    if response.status != 200:
        return Err("Package not found")

    # Parse SDN
    val sdn = rt_sdn_parse(response.body)
    parse_package_metadata(sdn)
```

**Day 3-4: Package Download**
- [ ] Download package tarball from registry
- [ ] Verify checksum
- [ ] Extract to cache
- [ ] Write tests

**Day 5: Local Index Cache**
- [ ] Cache index metadata locally: `~/.simple/cache/index/`
- [ ] TTL: 1 hour (configurable)
- [ ] Refresh on `simple update`

#### Week 2: Registry Commands

**Day 1-2: Search**
- [ ] `simple search <query>` - search packages
- [ ] Fuzzy matching on name + description
- [ ] Show package info (description, latest version, downloads)
- [ ] Write tests

**Example:**
```bash
$ simple search http
Found 5 packages:

  http (1.1.0) - HTTP client library
    https://github.com/simple-lang/http
    Downloads: 1.2k

  http_server (2.0.0) - HTTP server framework
    https://github.com/simple-lang/http_server
    Downloads: 850

  ...
```

**Day 3-4: Info**
- [ ] `simple info <package>` - show package details
- [ ] List all versions
- [ ] Show dependencies
- [ ] Show repository URL
- [ ] Write tests

**Example:**
```bash
$ simple info http
http 1.1.0
  HTTP client library for Simple

  Repository: https://github.com/simple-lang/http
  License: MIT
  Downloads: 1.2k

  Dependencies:
    url ^1.0
    tls ^2.0 (optional)

  Versions:
    1.1.0 (latest)
    1.0.0
```

**Day 5: Integration**
- [ ] `simple add http` resolves from registry
- [ ] `simple install` downloads from registry
- [ ] Update lockfile with registry checksums

#### Week 3: Registry Setup (GitHub)

**Day 1-3: Create Registry Repo**
- [ ] Create `simple-lang/registry` GitHub repo
- [ ] Add index structure: `index/{aa}/{bb}/{name}.sdn`
- [ ] Add example packages
- [ ] Write README with contribution guide

**Example index/ht/tp/http.sdn:**
```sdn
package:
  name: http
  description: HTTP client library
  repository: https://github.com/simple-lang/http
  license: MIT

versions |version, published, yanked, checksum, deps|
  1.0.0, 2024-12-01T00:00:00Z, false, sha256:abc123..., []
  1.1.0, 2024-12-15T00:00:00Z, false, sha256:def456..., [url>=1.0]
```

**Day 4-5: Publish Workflow (Basic)**
- [ ] `simple publish` command (basic)
- [ ] Create PR to registry repo
- [ ] Manual review process (for now)

### Deliverables

- [x] Sparse protocol client
- [x] Package download from registry
- [x] Local index cache
- [x] `simple search` command
- [x] `simple info` command
- [x] Registry repo on GitHub
- [x] Basic publish workflow

### Success Criteria

```bash
# Search for packages
simple search json
# → Shows packages matching "json"

# Add package from registry
simple add http ^1.0
# → Fetches metadata from registry
# → Updates simple.sdn

# Install downloads from registry
simple install
# → Downloads http-1.1.0.tar.gz
# → Stores in cache
# → Creates hard link to deps/
```

---

## Phase 6: PubGrub Resolver

**Duration:** 3-4 weeks
**Goal:** Replace backtracking with PubGrub for better errors + speed

### Tasks

#### Week 1: PubGrub Library Integration

**Day 1-2: Add Rust Dependency**
- [ ] Add `pubgrub = "0.2"` to runtime Cargo.toml
- [ ] Create FFI wrapper: `rust/runtime/src/value/ffi/pubgrub.rs`
- [ ] Expose to Simple: `lib/std/src/pubgrub_ffi.spl`
- [ ] Write tests

**Example:**
```rust
// rust/runtime/src/value/ffi/pubgrub.rs

use pubgrub::{solve, Dependencies, Range, Version};

#[no_mangle]
pub unsafe extern "C" fn rt_pubgrub_solve(
    root: *const c_char,
    deps_json: *const c_char,
) -> *mut c_char {
    // Parse dependencies from JSON
    // Call pubgrub::solve()
    // Return solution as JSON
}
```

**Day 3-5: Simple Integration**
- [ ] Create `src/app/package/pubgrub_resolver.spl`
- [ ] Convert Simple constraints to PubGrub format
- [ ] Call FFI
- [ ] Parse results
- [ ] Write tests

#### Week 2: Error Messages

**Day 1-3: Conflict Reporting**
- [ ] Parse PubGrub error messages
- [ ] Format for Simple users
- [ ] Show dependency chain
- [ ] Suggest fixes
- [ ] Write tests

**Example Output:**
```
Error: Cannot resolve dependencies

  Package 'json 2.0.1' requires url ^2.0
  But package 'http 1.1.0' requires url ^1.0

  Dependency chain:
    myapp 0.1.0 → http ^1.0 → url ^1.0
    myapp 0.1.0 → json ^2.0 → url ^2.0

  Possible solutions:
    1. Use json 2.0.0 (compatible with url ^1.0)
    2. Use http 1.2.0 (compatible with url ^2.0)
```

**Day 4-5: Integration Testing**
- [ ] Test on complex dependency graphs
- [ ] Measure performance vs backtracking
- [ ] Verify error messages are helpful

#### Week 3-4: Production Readiness

**Day 1-2: Edge Cases**
- [ ] Circular dependencies
- [ ] Optional dependencies
- [ ] Platform-specific dependencies
- [ ] Dev dependencies (don't affect resolution)

**Day 3-4: Performance**
- [ ] Benchmark on large projects (100+ packages)
- [ ] Optimize FFI calls
- [ ] Cache resolution results

**Day 5: Documentation**
- [ ] Document resolver behavior
- [ ] Add troubleshooting guide
- [ ] Update changelog

### Deliverables

- [x] PubGrub Rust library integrated
- [x] FFI wrapper for Simple
- [x] PubGrub resolver in Simple
- [x] Excellent error messages
- [x] 10x faster resolution (benchmark)
- [x] Edge cases handled

### Success Criteria

```bash
# Complex dependency conflict
simple add conflicting_package

Error: Cannot resolve dependencies
  Package 'A' requires B ^1.0
  But package 'C 2.0' requires B ^2.0

  Possible solutions:
    1. Use C 1.5 (compatible with B ^1.0)
    2. Upgrade A to 2.0 (removes B ^1.0 requirement)

# Fast resolution
time simple install
# Before (backtracking): 5.2s
# After (PubGrub): 0.3s
# → 17x faster
```

---

## Phase 7: Parallel HTTP/2

**Duration:** 1-2 weeks
**Goal:** 3-4x faster downloads with parallel HTTP/2

### Tasks

#### Week 1: Async Downloads

**Day 1-2: Tokio Integration**
- [ ] Add tokio FFI: `rust/runtime/src/value/ffi/async_http.rs`
- [ ] HTTP/2 client with reqwest
- [ ] Expose to Simple: `lib/std/src/http_ffi.spl`
- [ ] Write tests

**Example:**
```rust
// async_http.rs

use tokio::runtime::Runtime;
use reqwest::Client;

static RUNTIME: OnceLock<Runtime> = OnceLock::new();

#[no_mangle]
pub unsafe extern "C" fn rt_http_download_parallel(
    urls_json: *const c_char,
    max_concurrent: i32,
) -> *mut c_char {
    let runtime = RUNTIME.get_or_init(|| Runtime::new().unwrap());

    runtime.block_on(async {
        let client = Client::builder()
            .http2_prior_knowledge()
            .build()
            .unwrap();

        // Download all URLs in parallel
        // Return results as JSON
    });
}
```

**Day 3-4: Progress Bars**
- [ ] Add indicatif for terminal UI
- [ ] Show per-package progress
- [ ] Real-time download speeds
- [ ] Write tests

**Example:**
```
Downloading packages...
[████████████████──────] 8/10 (80%)
  ✓ http-1.1.0      [2.3 MB] (done)
  ✓ json-2.0.1      [890 KB] (done)
  ↓ crypto-3.1.0    [4.1 MB] 45% (1.8 MB/s)
  ↓ tls-2.5.0       [3.4 MB] 12% (2.1 MB/s)
```

**Day 5: Configuration**
- [ ] `~/.simple/config.sdn` for settings
- [ ] `max_concurrent_downloads`: 12 (default)
- [ ] `timeout_seconds`: 30
- [ ] `retry_count`: 3

#### Week 2: Testing & Optimization

**Day 1-2: Benchmarking**
- [ ] Measure download time with 1 vs 12 concurrent
- [ ] Test on slow networks
- [ ] Test on fast networks
- [ ] Verify HTTP/2 is being used

**Day 3-4: Integration**
- [ ] Update `simple install` to use parallel downloads
- [ ] Ensure cache works with parallel writes
- [ ] Handle network errors gracefully

**Day 5: Documentation**
- [ ] Update user guide
- [ ] Document configuration options

### Deliverables

- [x] Async HTTP/2 client
- [x] Parallel downloads (12 concurrent)
- [x] Progress bars
- [x] Configuration file
- [x] 3-4x faster downloads (benchmark)

### Success Criteria

```bash
# 10 packages, each 2MB, 10 Mbps connection
# Sequential: ~16s (one at a time)
# Parallel (12): ~4s (3-4x faster)

simple install
Downloading packages...
[████████████████──────] 8/10 (80%)
  ✓ http-1.1.0      [2.3 MB] (done)
  ↓ crypto-3.1.0    [4.1 MB] 45% (1.8 MB/s)
# → Total time: 4.2s (was 16s)
```

---

## Testing Strategy

### Unit Tests

Each component has SSpec tests:
- `manifest_spec.spl` - Manifest parsing
- `lockfile_spec.spl` - Lockfile generation
- `semver_spec.spl` - Version parsing
- `resolver_spec.spl` - Dependency resolution
- `cache_spec.spl` - Cache operations

### Integration Tests

End-to-end workflows:
- `install_spec.spl` - Full install workflow
- `add_spec.spl` - Add dependency workflow
- `update_spec.spl` - Update workflow

### Manual Testing

Real-world scenarios:
- Clone project with lockfile
- Add dependency and reinstall
- Resolve conflicts
- Use cache across multiple projects

### Performance Benchmarks

Track metrics:
- Cold install time (10 deps)
- Warm install time (all cached)
- Disk usage (with/without cache)
- Resolution time (complex graphs)

---

## Risk Mitigation

### Risk 1: Windows Hard Link Issues

**Risk:** Hard links require admin on older Windows

**Mitigation:**
- Automatic fallback to copy
- Document Windows developer mode
- Still works, just slower

### Risk 2: Git Dependency Complexity

**Risk:** Git operations can be slow/unreliable

**Mitigation:**
- Cache git clones
- Shallow clones where possible
- Clear error messages

### Risk 3: PubGrub Learning Curve

**Risk:** PubGrub is complex, may take longer than estimated

**Mitigation:**
- Start with backtracking (simpler)
- PubGrub is nice-to-have, not critical
- Can defer to later phase

### Risk 4: Registry Spam/Security

**Risk:** Public registry could be abused

**Mitigation:**
- Start with manual review (GitHub PR)
- Add automated checks later
- Namespacing (future)

---

## Success Metrics

### Phase 3.5 Success
- [ ] `simple install` works with path deps
- [ ] `simple install` works with git deps
- [ ] Lockfile is generated
- [ ] Lockfile is used on reinstall
- [ ] 10+ SSpec tests passing

### Phase 4 Success
- [ ] Global cache created on first use
- [ ] Hard links created successfully
- [ ] 70% disk savings measured
- [ ] Warm install <100ms

### Phase 5 Success
- [ ] `simple search` finds packages
- [ ] `simple add http` installs from registry
- [ ] Registry has 10+ packages

### Phase 6 Success
- [ ] PubGrub resolver works
- [ ] Error messages are helpful
- [ ] 10x faster than backtracking

### Phase 7 Success
- [ ] Parallel downloads work
- [ ] Progress bars show
- [ ] 3-4x faster downloads

---

## Next Steps

1. **Immediate:** Start Phase 3.5 (Dependency Foundation)
   - Create manifest parser
   - Implement lockfile
   - Build simple resolver

2. **Week 2-3:** Complete Phase 3.5
   - Path dependencies
   - Git dependencies
   - End-to-end testing

3. **Week 4-5:** Phase 4 (Global Cache)
   - Quick win: 70% disk savings
   - Major UX improvement

4. **Month 2-3:** Phases 5-7
   - Registry for ecosystem growth
   - PubGrub for better UX
   - Parallel downloads for speed

---

## Appendix: File Checklist

### New Files to Create

```
src/app/package/
├── manifest.spl          # Parse simple.sdn
├── lockfile.spl          # Generate/read simple.lock
├── semver.spl            # Version parsing/matching
├── resolver.spl          # Backtracking resolver
├── pubgrub_resolver.spl  # PubGrub resolver (Phase 6)
├── cache.spl             # Global cache management
├── registry.spl          # Registry protocol client
├── download.spl          # Parallel HTTP/2 downloads
├── types.spl             # Shared types
├── *_spec.spl            # Tests for each module

lib/std/src/
├── pubgrub_ffi.spl       # PubGrub FFI bindings
├── http_ffi.spl          # Async HTTP FFI bindings

rust/runtime/src/value/ffi/
├── pubgrub.rs            # PubGrub Rust wrapper
├── async_http.rs         # Tokio HTTP client

~/.simple/
├── cache/                # Global cache directory
│   ├── packages/
│   ├── git/
│   └── index/
├── config.sdn            # Configuration
└── credentials.sdn       # Registry auth tokens
```

### Files to Modify

```
src/app/package/
├── main.spl              # Add new commands
├── install.spl           # Use resolver + cache
├── build.spl             # No changes needed

Cargo.toml (add dependencies):
  pubgrub = "0.2"
  tokio = { version = "1", features = ["full"] }
  reqwest = { version = "0.11", features = ["http2"] }
  indicatif = "0.17"
```

---

**Plan Status:** Ready to Execute
**Start Date:** 2026-02-01
**Estimated Completion:** April 2026
