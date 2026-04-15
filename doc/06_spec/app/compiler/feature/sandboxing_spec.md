# Sandboxing & Isolation

**Feature ID:** #916-923 | **Category:** Language Features | **Status:** ✅ Implemented

_Source: `test/feature/usage/sandboxing_spec.spl`_

---

## Overview

Simple provides two complementary isolation models for secure code execution:

### Runtime Sandboxing (#916-919)
- **Resource Limits** - CPU, memory, file descriptors, threads
- **Network Isolation** - Block/allow network access by domain
- **Filesystem Isolation** - Restrict read/write paths

### Environment Isolation (#920-923) - Planned
- **Virtual Environments** - Per-project dependencies
- **Package Isolation** - Isolated package installations
- **Reproducible Builds** - Lock files for exact versions

## CLI Usage

```bash
# Basic sandboxing
simple script.spl --sandbox

# Resource limits
simple script.spl --time-limit 30 --memory-limit 100M

# Network isolation
simple script.spl --no-network
simple script.spl --network-allow github.com,api.example.com
simple script.spl --network-block malicious.com

# Filesystem isolation
simple script.spl --read-only /tmp,/usr/lib
simple script.spl --read-write /app/data
```

## Related Specifications

- **BDD Testing** - Test framework integration
- **Build Audit** - Security auditing

## Available APIs

Process execution for sandbox testing:
```simple
import sys.process

# Run command with timeout
val exit_code = process.run_timeout("simple", ["script.spl", "--time-limit", "5"], 10000)

# Capture output
val result = process.output("simple", ["--version"])
if result.is_success():
    print(result.stdout)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 14 |

## Test Structure

### Resource Limits

- ✅ limits CPU time for long-running scripts
- ✅ limits memory allocation
- ✅ limits file descriptors
- ✅ limits thread creation
### Network Isolation

- ✅ blocks all network access with --no-network
- ✅ allows only specified domains with --network-allow
- ✅ blocks specified domains with --network-block
### Filesystem Isolation

- ✅ restricts to read-only paths
- ✅ allows read-write to specific paths
- ✅ uses overlay filesystem for isolation
### Combined Sandbox Configuration

- ✅ applies multiple restrictions simultaneously
- ✅ provides secure defaults with --sandbox
### Environment Isolation

- ✅ creates isolated virtual environments
- ✅ supports lock files for reproducibility

