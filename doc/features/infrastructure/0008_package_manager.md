# Feature #8: Package Manager

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #8 |
| **Feature Name** | Package Manager |
| **Category** | Infrastructure |
| **Difficulty** | 3 (Medium) |
| **Status** | Complete |
| **Implementation** | Rust |

## Description

UV-style fast package management for Simple language. Supports simple.toml manifests, lock files, path/git dependencies, global cache, and dependency resolution.

## Specification

[doc/architecture/README.md](../../architecture/README.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/pkg/src/manifest.rs` | simple.toml parsing |
| `src/pkg/src/lock.rs` | simple.lock format |
| `src/pkg/src/cache.rs` | Global cache with hard links |
| `src/pkg/src/resolver/graph.rs` | Topological ordering |

## CLI Commands

| Command | Description |
|---------|-------------|
| simple init | Create new project with simple.toml |
| simple add <pkg> | Add dependency to manifest |
| simple install | Install all dependencies |
| simple update | Update dependencies to latest |
| simple list | List installed dependencies |
| simple tree | Show dependency tree |
| simple cache | Manage global cache |

## Manifest Format

```toml
[package]
name = "my-app"
version = "1.0.0"

[dependencies]
std = "^1.0"
json = { version = "^0.5", features = ["async"] }

[dev-dependencies]
test = "^0.1"
```

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/infrastructure/package_manager_spec.spl` | BDD spec (16 tests) |

## Dependencies

- Depends on: None (standalone component)
- Required by: None

## Notes

CLI commands: init, add, install, update, list, tree, cache. Supports semantic versioning and topological dependency ordering.
