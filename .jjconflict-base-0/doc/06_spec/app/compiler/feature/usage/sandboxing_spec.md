# Sandboxing & Isolation

Simple provides two complementary isolation models for secure code execution:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #916-923 |
| Status | Runtime Complete (#916-919), Environment Planned (#920-923) |
| Source | `test/feature/usage/sandboxing_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

**Keywords:** sandbox, isolation, security, environment, virtualenv
**Last Updated:** 2026-01-18
**Topics:** security, tooling
**Migrated From:** doc/06_spec/sandboxing.md

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
simple script.spl --sandbox

simple script.spl --time-limit 30 --memory-limit 100M

simple script.spl --no-network
simple script.spl --network-allow github.com,api.example.com
simple script.spl --network-block malicious.com

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

val exit_code = process.run_timeout("simple", ["script.spl", "--time-limit", "5"], 10000)

val result = process.output("simple", ["--version"])
if result.is_success():
print(result.stdout)
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/sandboxing/result.json` |

## Scenarios

- limits CPU time for long-running scripts
- limits memory allocation
- limits file descriptors
- limits thread creation
- blocks all network access with --no-network
- allows only specified domains with --network-allow
- blocks specified domains with --network-block
- restricts to read-only paths
- allows read-write to specific paths
- uses overlay filesystem for isolation
- applies multiple restrictions simultaneously
- provides secure defaults with --sandbox
- creates isolated virtual environments
- supports lock files for reproducibility
