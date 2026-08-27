# Sandboxing & Isolation

> Simple provides two complementary isolation models for secure code execution:

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
| Source | `test/feature/usage/sandboxing_spec.spl` |
| Updated | 2026-08-26 |
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
use std.spec.step

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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- limits CPU time for long-running scripts


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("limits CPU time for long-running scripts")
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

- limits memory allocation


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("limits memory allocation")
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

- limits file descriptors


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("limits file descriptors")
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

- limits thread creation


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("limits thread creation")
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

- blocks all network access with --no-network


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("blocks all network access with --no-network")
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

- allows only specified domains with --network-allow


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows only specified domains with --network-allow")
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

- blocks specified domains with --network-block


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("blocks specified domains with --network-block")
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

- restricts to read-only paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("restricts to read-only paths")
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

- allows read-write to specific paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows read-write to specific paths")
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

- uses overlay filesystem for isolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses overlay filesystem for isolation")
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

- applies multiple restrictions simultaneously


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("applies multiple restrictions simultaneously")
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

- provides secure defaults with --sandbox


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("provides secure defaults with --sandbox")
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

- creates isolated virtual environments


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates isolated virtual environments")
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

- supports lock files for reproducibility


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("supports lock files for reproducibility")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f3accadc547a78a21e8b53f97bc4625d3e2aa16847f5a3224425d355f9562a41`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f3accadc547a78a21e8b53f97bc4625d3e2aa16847f5a3224425d355f9562a41`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f3accadc547a78a21e8b53f97bc4625d3e2aa16847f5a3224425d355f9562a41`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/sandboxing_spec.spl
mirror: doc/06_spec/feature/usage/sandboxing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/sandboxing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/sandboxing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/sandboxing_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'limits CPU time for long-running scripts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/sandboxing_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'limits memory allocation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/sandboxing_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'limits file descriptors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
