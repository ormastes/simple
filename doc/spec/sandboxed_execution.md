# Sandboxed Execution Specification (#916-923)

**Status:** ✅ Runtime Complete (#916-919), 📋 Environment Planned (#920-923)
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

**See:** [sandbox_environment.md](sandbox_environment.md) for detailed specification

### Runtime Sandboxing (#916-919)
**Like Docker containers:**
- Process isolation with namespaces
- Resource limits (CPU, memory, time)
- Network isolation
- Filesystem restrictions
- Secure execution of untrusted code

**See:** [sandbox_runtime.md](sandbox_runtime.md) for detailed specification

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

## Feature Documentation

### Runtime Sandboxing Features (#916-919) ✅

All runtime sandboxing features are **complete** and implemented:

| Feature | Status | Description |
|---------|--------|-------------|
| #916: Resource Limits | ✅ | CPU time, memory, file descriptors |
| #917: Network Isolation | ✅ | Block network by default, allowlist support |
| #918: Filesystem Isolation | ✅ | Read-only by default, directory allowlist |
| #919: `simple run --sandbox` | ✅ | CLI integration with profiles |

**See:** [sandbox_runtime.md](sandbox_runtime.md) for complete details

### Environment Isolation Features (#920-923) 📋

Environment isolation features are **planned**:

| Feature | Status | Description |
|---------|--------|-------------|
| #920: Environment Creation | 📋 | Create, activate, manage environments |
| #921: Package Isolation | 📋 | Per-environment package installation |
| #922: Reproducibility | 📋 | Lock files, export/import |
| #923: Integration | 📋 | Environment + sandbox combined |

**See:** [sandbox_environment.md](sandbox_environment.md) for complete specification

## Implementation

**See:** [sandbox_implementation.md](sandbox_implementation.md) for:
- Rust dependencies and platform-specific implementations
- Environment manager implementation
- Runtime sandbox backends (Linux, macOS, Windows, Docker)
- Library usage and performance comparison
- Implementation plan and file structure
- Success metrics and references

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

## Summary

This specification covers **8 features (#916-923)** providing complete isolation for Simple projects:

### Environment Isolation (Virtualenv-Style) - #920-923
**Like Python's venv:** Dependency isolation, project-local packages, reproducible builds

### Runtime Sandboxing (Container-Style) - #916-919
**Like Docker:** Process isolation, resource limits, security restrictions

This provides the **best of both worlds**: dependency isolation (like Python venv) + runtime security (like containers), making Simple ideal for LLM-assisted development with safe execution of generated code.
