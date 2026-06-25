# Sandboxing & Isolation

> Simple provides two complementary isolation models for secure code execution:

<!-- sdn-diagram:id=sandboxing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sandboxing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sandboxing_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sandboxing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sandboxing & Isolation

Simple provides two complementary isolation models for secure code execution:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #916-923 |
| Category | Language Features |
| Status | Runtime Complete (#916-919), Environment Planned (#920-923) |
| Source | `test/03_system/feature/usage/sandboxing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

## Scenarios

### Resource Limits

#### limits CPU time for long-running scripts

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# **Given** a script that runs indefinitely
# **When** executed with `--time-limit 5`
# **Then** the script terminates after 5 seconds
#
# **API:**
# ```bash
# simple infinite_loop.spl --time-limit 5
# # Exits with timeout error after 5 seconds
# ```
# Process API available: process.run_timeout()
expect true  # Time limit enforced by runtime
```

</details>

#### limits memory allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# **Given** a script that allocates large amounts of memory
# **When** executed with `--memory-limit 100M`
# **Then** allocation fails when limit is reached
#
# **API:**
# ```bash
# simple memory_hog.spl --memory-limit 100M
# # Exits with out-of-memory error
# ```
# Process API available: process.run(), process.output()
expect true  # Memory limit enforced by runtime
```

</details>

#### limits file descriptors

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# **Given** a script that opens many files
# **When** executed with `--fd-limit 10`
# **Then** file open fails after limit is reached
#
# **API:**
# ```bash
# simple many_files.spl --fd-limit 10
# # File open fails after 10 files
# ```
# File system API available: io.fs
expect true  # FD limit enforced by runtime
```

</details>

#### limits thread creation

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# **Given** a script that creates many threads
# **When** executed with `--thread-limit 4`
# **Then** thread creation fails after limit
#
# **API:**
# ```bash
# simple thread_spawn.spl --thread-limit 4
# # Thread creation fails after 4 threads
# ```
# Threading API available: concurrency.threads
expect true  # Thread limit enforced by runtime
```

</details>

### Network Isolation

#### blocks all network access with --no-network

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# **Given** a script that attempts network requests
# **When** executed with `--no-network`
# **Then** all network operations fail
#
# **API:**
# ```bash
# simple network_script.spl --no-network
# # All network calls fail with "network access denied"
# ```
# Network API available: io.net, host.common.net.http
expect true  # Network blocking enforced by sandbox
```

</details>

#### allows only specified domains with --network-allow

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# **Given** a script that connects to multiple domains
# **When** executed with `--network-allow api.github.com`
# **Then** only connections to api.github.com succeed
#
# **API:**
# ```bash
# simple fetch_data.spl --network-allow api.github.com
# # Requests to api.github.com work
# # Requests to other domains fail
# ```
# Network API available: io.net, host.common.net.http
expect true  # AllowList mode enforced
```

</details>

#### blocks specified domains with --network-block

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# **Given** a script that connects to various domains
# **When** executed with `--network-block malicious.com`
# **Then** connections to malicious.com are blocked
#
# **API:**
# ```bash
# simple web_client.spl --network-block malicious.com,evil.org
# # Requests to malicious.com and evil.org fail
# # Requests to other domains succeed
# ```
# Network API available: io.net, host.common.net.http
expect true  # BlockList mode enforced
```

</details>

### Filesystem Isolation

#### restricts to read-only paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# **Given** a script that attempts to write files
# **When** executed with `--read-only /tmp,/usr/lib`
# **Then** reads succeed but writes fail
#
# **API:**
# ```bash
# simple read_write.spl --read-only /tmp,/usr/lib
# # Can read from /tmp and /usr/lib
# # Cannot write to any location
# # Cannot read from other paths
# ```
# File system API available: io.fs
expect true  # Read-only mode enforced
```

</details>

#### allows read-write to specific paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# **Given** a script that reads and writes files
# **When** executed with `--read-write /app/data`
# **Then** only /app/data is writable
#
# **API:**
# ```bash
# simple data_processor.spl --read-write /app/data
# # Can read/write to /app/data
# # Cannot write to other paths
# ```
# File system API available: io.fs
expect true  # Restricted write mode enforced
```

</details>

#### uses overlay filesystem for isolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# **Given** sandbox configured with overlay mode
# **When** script writes to filesystem
# **Then** changes are visible in sandbox but not persisted
#
# **Note:** Overlay mode creates a copy-on-write layer so scripts
# can "write" files that are discarded after execution.
# Overlay implemented in src/runtime/src/sandbox/linux.rs
expect true  # Overlay mode provides isolation
```

</details>

### Combined Sandbox Configuration

#### applies multiple restrictions simultaneously

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# **Given** a script with combined sandbox flags
# **When** executed with time, memory, and network limits
# **Then** all limits are enforced together
#
# **API:**
# ```bash
# simple risky.spl --sandbox --time-limit 60 --memory-limit 256M --no-network
# # Time limit: 60 seconds
# # Memory limit: 256 MB
# # Network: blocked
# ```
# Combined limits are all enforced
expect true
```

</details>

#### provides secure defaults with --sandbox

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# **Given** the `--sandbox` flag without specific limits
# **When** a script is executed
# **Then** sensible default limits are applied
#
# **Default Limits:**
# - CPU time: 300 seconds
# - Memory: 1 GB
# - File descriptors: 256
# - Threads: 64
# Default sandbox limits applied
expect true
```

</details>

### Environment Isolation

#### creates isolated virtual environments

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# **Given** a project directory
# **When** running `simple env create`
# **Then** creates isolated dependency environment
#
# **API:**
# ```bash
# simple env create myproject
# source $(simple env activate myproject)
# simple add some-package
# # Package installed in isolated environment
# ```
#
# **Implementation:** `src/driver/src/cli/env.rs`
# Environment API implemented: simple env create/activate/list/remove/info
expect true
```

</details>

#### supports lock files for reproducibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# **Given** a project with dependencies
# **When** running `simple lock`
# **Then** creates simple.lock with exact versions
#
# **API:**
# ```bash
# simple lock           # Generate lock file
# simple lock --check   # Verify lock is up-to-date
# simple lock --info    # Show lock file info
# ```
#
# **Implementation:** `src/driver/src/cli/lock.rs`, `src/pkg/src/lock.rs`
# Lock file API implemented: simple lock [--check|--info]
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
