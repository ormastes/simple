# Package Manager

*Source: `simple/std_lib/test/features/infrastructure/package_manager_spec.spl`*

---

# Package Manager

**Feature ID:** #8
**Category:** Infrastructure
**Difficulty:** Level 4/5
**Status:** Complete
**Implementation:** Rust

## Overview

UV-style fast package management for Simple language. Supports simple.toml manifests,
lock files, path/git dependencies, global cache, and dependency resolution.

## Syntax

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

## Implementation

**Files:**
- src/pkg/src/lib.rs - Main package manager module
- src/pkg/src/manifest.rs - Manifest parsing (simple.toml)
- src/pkg/src/lock.rs - Lock file handling
- src/pkg/src/version.rs - Semantic versioning
- src/pkg/src/cache.rs - Global package cache
- src/pkg/src/resolver/graph.rs - Dependency graph resolution

**Tests:**
- src/pkg/tests/manifest_tests.rs

**Dependencies:** None
**Required By:** None

## Notes

CLI commands: init, add, install, update, list, tree, cache. Supports semantic
versioning and topological dependency ordering.
