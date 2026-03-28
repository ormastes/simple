# Comprehensive Skip/Ignore System - Design Summary

**Date:** 2026-02-08
**Status:** DESIGN
**Implementation Plan:** `skip_ignore_implementation_plan.md`

## Overview

A **comprehensive test skip/ignore system** that supports ALL possible execution conditions across 12 dimensions.

## Design Principles

### 1. Semantic Distinction

| Type | Meaning | Timeline | Counted | Output |
|------|---------|----------|---------|--------|
| `@skip` | **Will implement in future** | Temporary (TODO) | ✅ Yes | "SKIP" message |
| `@ignore` | **Fundamentally not supported** | Permanent (won't fix) | ❌ No | Silent |

### 2. Condition Dimensions (12 Total)

```simple
@skip(
    # 1. Platform
    platforms: ["windows", "linux", "macos", "unix", "bsd"],

    # 2. Runtime Mode
    runtimes: ["interpreter", "compiled", "jit", "aot"],

    # 3. Build Profile
    profiles: ["debug", "release", "bootstrap", "test"],

    # 4. Architecture
    architectures: ["x86_64", "aarch64", "arm64", "riscv64", "wasm32"],

    # 5. Feature Flags
    features: ["generics", "async", "macros", "effects", "inline_asm"],

    # 6. Compiler Version
    version: ">= 0.5.0",

    # 7. Hardware Capabilities
    hardware: ["gpu", "simd", "avx2", "neon", "multi_core"],

    # 8. Dependencies
    requires: ["torch", "numpy", "sqlite3"],

    # 9. Environment Variables
    env_vars: {"CI": "true", "SIMPLE_COVERAGE": nil},

    # 10. File System Capabilities
    fs_features: ["symlinks", "permissions", "case_sensitive", "xattr"],

    # 11. Network Availability
    network: true,

    # 12. Tags/Timing
    tags: ["slow", "integration", "e2e"],

    reason: "Detailed explanation"
)
```

## Architecture

```
Test Execution
    │
    ▼
┌─────────────────────────────────────┐
│  Decorator: skip() / ignore()       │
│  - Parse all 12 condition types     │
│  - Create SkipCondition struct      │
└─────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────┐
│  Environment Detection (Cached)     │
│  ┌─────────────────────────────┐   │
│  │ 1. Platform  ✅ DONE        │   │
│  │ 2. Runtime   ⏳ TODO        │   │
│  │ 3. Profile   ⏳ TODO        │   │
│  │ 4. Architecture ⏳ TODO     │   │
│  │ 5. Features  ⏳ TODO        │   │
│  │ 6. Hardware  ⏳ TODO        │   │
│  │ 7. Dependencies ⏳ TODO     │   │
│  │ 8. Environment ⏳ TODO      │   │
│  │ 9. File System ⏳ TODO      │   │
│  │ 10. Network  ⏳ TODO        │   │
│  │ 11. Version  ⏳ TODO        │   │
│  │ 12. Tags     ⏳ TODO        │   │
│  └─────────────────────────────┘   │
└─────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────┐
│  Condition Evaluator                │
│  - Check ALL conditions             │
│  - OR logic: ANY match = skip       │
│  - Return: run / skip / ignore      │
└─────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────┐
│  Test Execution                     │
│  - Run test: Normal execution       │
│  - Skip test: Count + print "SKIP"  │
│  - Ignore test: Silent (no output)  │
└─────────────────────────────────────┘
```

## Usage Examples

### Example 1: Platform + Runtime
```simple
# Skip on Windows interpreter (will implement)
val skip_win_interp = skip(
    platforms: ["windows"],
    runtimes: ["interpreter"],
    reason: "Not yet ported to Windows interpreter"
)

skip_win_interp("file permissions", fn():
    chmod("/tmp/file", 0o644)
)
```

### Example 2: Hardware Requirements
```simple
# Ignore GPU tests without GPU (fundamental limitation)
val ignore_no_gpu = ignore(
    hardware: ["gpu"],
    reason: "CUDA only, no CPU implementation"
)

ignore_no_gpu("GPU kernel test", fn():
    launch_cuda_kernel()
)
```

### Example 3: Feature Flags
```simple
# Skip async tests if feature disabled
val skip_no_async = skip(
    features: ["async"],
    reason: "Async runtime not initialized"
)

skip_no_async("async HTTP test", fn():
    await fetch("https://api.example.com")
)
```

### Example 4: Complex Multi-Condition
```simple
# Skip CI network tests in debug builds
val skip_ci_network = skip(
    network: true,
    env_vars: {"CI": "true"},
    profiles: ["debug"],
    reason: "Network tests only in CI debug"
)

skip_ci_network("API integration", fn():
    val response = http_get("https://api.example.com")
    check(response.status == 200)
)
```

### Example 5: Version Constraints
```simple
# Skip on old compiler versions
val skip_old = skip(
    version: "< 0.5.0",
    reason: "Requires v0.5.0+ for new syntax"
)

skip_old("new syntax test", fn():
    val x = if cond: 1 else: 2
)
```

### Example 6: File System Features
```simple
# Ignore permission tests on FAT32 (fundamental)
val ignore_fat32 = ignore(
    fs_features: ["permissions"],
    reason: "FAT32 has no permission system"
)

ignore_fat32("chmod test", fn():
    chmod("file.txt", 0o600)
)
```

## Implementation Modules

| Module | Purpose | Lines | Status |
|--------|---------|-------|--------|
| `src/lib/spec/env_detect.spl` | Environment detection (all 12 types) | ~400 | ⏳ TODO |
| `src/lib/spec/condition.spl` | `SkipCondition` struct + evaluator | ~150 | ⏳ TODO |
| `src/lib/spec/decorators.spl` | `skip()`, `ignore()`, `only_on()`, `skip_if()` | ~200 | ⏳ TODO |
| `src/lib/spec/builder.spl` | Fluent `TestBuilder` API | ~120 | ⏳ TODO |
| `test/lib/std/spec/skip_spec.spl` | Unit tests | ~500 | ⏳ TODO |

## Detection Functions

### Platform Detection ✅ DONE
```simple
fn is_windows() -> bool
fn is_linux() -> bool
fn is_macos() -> bool
fn is_unix() -> bool
```

### Runtime Detection ⏳ TODO
```simple
fn is_interpreter() -> bool
fn is_compiled() -> bool
fn is_jit() -> bool
fn get_build_profile() -> text  # "debug", "release", etc.
```

### Architecture Detection ⏳ TODO
```simple
fn is_x86_64() -> bool
fn is_aarch64() -> bool
fn is_arm64() -> bool
fn is_riscv64() -> bool
fn is_wasm32() -> bool
fn get_pointer_size() -> i32  # 32 or 64
```

### Feature Detection ⏳ TODO
```simple
fn has_generics() -> bool
fn has_async() -> bool
fn has_macros() -> bool
fn has_effects() -> bool
fn has_inline_asm() -> bool
```

### Hardware Detection ⏳ TODO
```simple
fn has_gpu() -> bool
fn has_cuda() -> bool
fn has_simd() -> bool
fn has_avx2() -> bool
fn has_neon() -> bool
fn get_cpu_cores() -> i32
```

### Dependency Detection ⏳ TODO
```simple
fn has_module(name: text) -> bool
fn has_library(name: text) -> bool
fn get_library_version(name: text) -> text
```

### Environment Detection ⏳ TODO
```simple
fn is_ci() -> bool
fn get_env(key: text) -> text?
fn has_env(key: text) -> bool
```

### File System Detection ⏳ TODO
```simple
fn has_symlinks() -> bool
fn has_permissions() -> bool
fn is_case_sensitive() -> bool
fn has_xattr() -> bool
```

### Network Detection ⏳ TODO
```simple
fn has_network() -> bool
fn can_reach(host: text) -> bool
```

### Version Detection ⏳ TODO
```simple
fn get_compiler_version() -> text
fn check_version(constraint: text) -> bool  # ">= 0.5.0"
```

## Performance Requirements

| Operation | Target | Current |
|-----------|--------|---------|
| Platform detection (cached) | < 0.1ms | ~0.5ms ✅ |
| Full environment detection (first call) | < 10ms | N/A |
| Full environment detection (cached) | < 1ms | N/A |
| Condition evaluation | < 0.1ms | N/A |
| Total overhead per test | < 1ms | N/A |

## Timeline

| Week | Phase | Deliverables |
|------|-------|--------------|
| 1-2 | Foundation | Platform ✅, Runtime, Architecture, Features detection |
| 3-4 | Detection Complete | Hardware, Dependencies, Environment, FS, Network, Version |
| 5 | Core Logic | `SkipCondition` struct, comprehensive evaluator |
| 6 | Decorators | `skip()`, `ignore()`, `only_on()`, `skip_if()` |
| 7 | Syntax Sugar | `TestBuilder` fluent API |
| 8 | Documentation | API docs, user guide, migration guide, examples |
| 9-12 | Parser (Future) | `@skip(...)` native syntax |

**Total:** 8 weeks for comprehensive function-based system

## Success Metrics

| Metric | Target |
|--------|--------|
| Condition types supported | 12/12 ✅ |
| Detection accuracy | 100% |
| Performance overhead | < 1ms per test |
| Tests using new system | 500+ |
| Documentation coverage | 100% |
| Unit test coverage | > 95% |
| Migration from old syntax | 100% |

## Migration Path

### Phase 1: Deprecate Old Functions
```simple
# Old (deprecated)
skip_on_windows("test", fn(): ...)
skip_on_interpreter("test", fn(): ...)

# New (comprehensive)
val skip_win = skip(platforms: ["windows"])
skip_win("test", fn(): ...)

val skip_interp = skip(runtimes: ["interpreter"])
skip_interp("test", fn(): ...)
```

### Phase 2: Auto-Migration Tool
```bash
simple migrate --skip-decorators test/
```

Converts all old `skip_on_*()` calls to new decorator syntax.

## Benefits

1. **Comprehensive**: Covers ALL execution conditions
2. **Clear Semantics**: skip (TODO) vs ignore (won't fix)
3. **Flexible**: Supports complex multi-condition logic
4. **Performant**: < 1ms overhead with caching
5. **Maintainable**: Track technical debt (skipped tests)
6. **Discoverable**: Clear API, good docs
7. **Extensible**: Easy to add new condition types

## Next Steps

1. Complete environment detection (Weeks 1-4)
2. Implement core logic (Week 5)
3. Implement decorators (Week 6)
4. Add syntax sugar (Week 7)
5. Write documentation (Week 8)
6. Migrate existing tests
7. Future: Parser attributes (Weeks 9-12)
