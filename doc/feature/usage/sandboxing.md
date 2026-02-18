# Sandboxing & Isolation
*Source:* `test/feature/usage/sandboxing_spec.spl`
**Feature IDs:** #916-923  |  **Status:** ✅ Implemented

## Overview



**Last Updated:** 2026-01-18
**Topics:** security, tooling
**Migrated From:** doc/spec/sandboxing.md

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

## Feature: Resource Limits

**Given** a script that creates many threads
        **When** executed with `--thread-limit 4`
        **Then** thread creation fails after limit

        **API:**
        ```bash
        simple thread_spawn.spl --thread-limit 4
        # Thread creation fails after 4 threads
        ```

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | limits CPU time for long-running scripts | pass |
| 2 | limits memory allocation | pass |
| 3 | limits file descriptors | pass |
| 4 | limits thread creation | pass |

**Example:** limits CPU time for long-running scripts
    Then  expect true  # Time limit enforced by runtime

**Example:** limits memory allocation
    Then  expect true  # Memory limit enforced by runtime

**Example:** limits file descriptors
    Then  expect true  # FD limit enforced by runtime

**Example:** limits thread creation
    Then  expect true  # Thread limit enforced by runtime

## Feature: Network Isolation

**Given** a script that connects to various domains
        **When** executed with `--network-block malicious.com`
        **Then** connections to malicious.com are blocked

        **API:**
        ```bash
        simple web_client.spl --network-block malicious.com,evil.org
        # Requests to malicious.com and evil.org fail
        # Requests to other domains succeed
        ```

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | blocks all network access with --no-network | pass |
| 2 | allows only specified domains with --network-allow | pass |
| 3 | blocks specified domains with --network-block | pass |

**Example:** blocks all network access with --no-network
    Then  expect true  # Network blocking enforced by sandbox

**Example:** allows only specified domains with --network-allow
    Then  expect true  # AllowList mode enforced

**Example:** blocks specified domains with --network-block
    Then  expect true  # BlockList mode enforced

## Feature: Filesystem Isolation

**Given** sandbox configured with overlay mode
        **When** script writes to filesystem
        **Then** changes are visible in sandbox but not persisted

        **Note:** Overlay mode creates a copy-on-write layer so scripts
        can "write" files that are discarded after execution.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | restricts to read-only paths | pass |
| 2 | allows read-write to specific paths | pass |
| 3 | uses overlay filesystem for isolation | pass |

**Example:** restricts to read-only paths
    Then  expect true  # Read-only mode enforced

**Example:** allows read-write to specific paths
    Then  expect true  # Restricted write mode enforced

**Example:** uses overlay filesystem for isolation
    Then  expect true  # Overlay mode provides isolation

## Feature: Combined Sandbox Configuration

**Given** the `--sandbox` flag without specific limits
        **When** a script is executed
        **Then** sensible default limits are applied

        **Default Limits:**
        - CPU time: 300 seconds
        - Memory: 1 GB
        - File descriptors: 256
        - Threads: 64

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | applies multiple restrictions simultaneously | pass |
| 2 | provides secure defaults with --sandbox | pass |

**Example:** applies multiple restrictions simultaneously
    Then  expect true

**Example:** provides secure defaults with --sandbox
    Then  expect true

## Feature: Environment Isolation

**Given** a project with dependencies
        **When** running `simple lock`
        **Then** creates simple.lock with exact versions

        **API:**
        ```bash
        simple lock           # Generate lock file
        simple lock --check   # Verify lock is up-to-date
        simple lock --info    # Show lock file info
        ```

        **Implementation:** `src/driver/src/cli/lock.rs`, `src/pkg/src/lock.rs`

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates isolated virtual environments | pass |
| 2 | supports lock files for reproducibility | pass |

**Example:** creates isolated virtual environments
    Then  expect true

**Example:** supports lock files for reproducibility
    Then  expect true


