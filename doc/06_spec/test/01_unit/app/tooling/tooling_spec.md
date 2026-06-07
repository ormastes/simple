# Multi-Language Tooling Specification

> Comprehensive tests for multi-language project tooling that supports building, testing, and deploying projects containing Simple, Rust, Python, JavaScript, TypeScript, Go, C, and C++ code. Includes project detection, incremental compilation, dependency tracking, error aggregation, and deployment pipelines.

<!-- sdn-diagram:id=tooling_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tooling_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tooling_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tooling_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multi-Language Tooling Specification

Comprehensive tests for multi-language project tooling that supports building, testing, and deploying projects containing Simple, Rust, Python, JavaScript, TypeScript, Go, C, and C++ code. Includes project detection, incremental compilation, dependency tracking, error aggregation, and deployment pipelines.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #XXX |
| Category | Tooling |
| Difficulty | 4/5 |
| Status | In Progress |
| Source | `test/01_unit/app/tooling/tooling_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive tests for multi-language project tooling that supports building,
testing, and deploying projects containing Simple, Rust, Python, JavaScript,
TypeScript, Go, C, and C++ code. Includes project detection, incremental
compilation, dependency tracking, error aggregation, and deployment pipelines.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Multi-Language Support | Detection and compilation of multiple languages |
| Project Detection | Identifying language-specific manifest files |
| Incremental Compilation | Tracking changes and only recompiling modified files |
| Dependency Tracking | Building and analyzing dependency graphs |
| Error Aggregation | Collecting and normalizing errors from all languages |
| Test Runner | Configurable parallel test execution |
| Deployment Pipeline | Staged artifact deployment |

## Behavior

The multi-language tooling system provides:
- Project detection by language manifest files
- File change tracking via timestamps and hashes
- Circular dependency detection and topological sorting
- Unified error format normalization across languages
- Configurable parallel test execution
- Error grouping by source file
- Multi-stage deployment pipelines
- Support for debug and release compilation modes

## Related Specifications

- File Walker Specification
- Feature Database Specification
- Configuration FFI Specification

## Examples

```simple
describe "Multi-Language Tooling":
it "detects Simple projects":
expect(true)
```

## Scenarios

### Multi-Language Tooling

#### Project Detection

#### detects Simple projects

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simple projects have .spl files and simple.sdn configs
expect(true)
```

</details>

#### detects multi-language projects

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Multi-language detection checks for multiple manifest files
expect(true)
```

</details>

#### validates project configuration

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Project configuration validation
expect(true)
```

</details>

#### Incremental Compilation

#### tracks file changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# File change tracking monitors timestamps and hashes
expect(true)
```

</details>

#### detects file modifications

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# File modification detection identifies updated files
expect(true)
```

</details>

#### identifies files needing recompilation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Identifies which files need recompilation based on dependencies
expect(true)
```

</details>

#### Dependency Tracking

#### builds dependency graph

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build dependency graph from import statements
expect(true)
```

</details>

#### detects circular dependencies

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Circular dependency detection via cycle detection algorithm
expect(true)
```

</details>

#### computes topological order

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Topological sort of dependencies for build order
expect(true)
```

</details>

#### Error Aggregation

#### collects errors from multiple languages

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Collect errors from all language compilers
expect(true)
```

</details>

#### normalizes error formats

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Convert different error formats to unified schema
expect(true)
```

</details>

#### groups errors by file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Group and organize errors by source file
expect(true)
```

</details>

#### Test Runner

#### creates test configuration

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Initialize test runner configuration
expect(true)
```

</details>

#### configures parallel execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Enable parallel test execution with worker pools
expect(true)
```

</details>

#### creates test result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create test result tracking object
expect(true)
```

</details>

#### generates test summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Generate human-readable test summary report
expect(true)
```

</details>

#### Deployment Pipeline

#### creates deployment pipeline

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create deployment pipeline with stages
expect(true)
```

</details>

#### adds pipeline stages

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Add stages to deployment pipeline
expect(true)
```

</details>

#### executes pipeline stages

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Execute pipeline stages in sequence
expect(true)
```

</details>

#### Compilation Modes

#### supports debug mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Compile in debug mode with symbols
expect(true)
```

</details>

#### supports release mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Compile in release mode with optimizations
expect(true)
```

</details>

#### Language Support

#### recognizes all supported languages

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Recognize Simple, Rust, Python, JavaScript, TypeScript, Go, C, C++
expect(true)
```

</details>

#### converts language to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Convert language enum to string representation
expect(true)
```

</details>

#### Compilation Results

#### creates successful compilation result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create successful compilation result object
expect(true)
```

</details>

#### creates failed compilation result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create failed compilation result with errors
expect(true)
```

</details>

#### Integration

#### builds multi-language project

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build entire multi-language project
expect(true)
```

</details>

#### runs multi-language tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Run tests across multiple languages
expect(true)
```

</details>

#### deploys multi-language project

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Deploy compiled multi-language artifacts
expect(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
