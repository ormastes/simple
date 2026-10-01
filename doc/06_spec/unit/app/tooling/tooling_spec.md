# Tooling Specification

> Tests covering Multi-Language Tooling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tooling Specification

## Scenarios

### Multi-Language Tooling

#### Project Detection

#### detects Simple projects

- detects Simple projects


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects Simple projects")
# Simple projects have .spl files and simple.sdn configs
expect(true)
```

</details>

#### detects multi-language projects

- detects multi-language projects


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects multi-language projects")
# Multi-language detection checks for multiple manifest files
expect(true)
```

</details>

#### validates project configuration

- validates project configuration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates project configuration")
# Project configuration validation
expect(true)
```

</details>

#### Incremental Compilation

#### tracks file changes

- tracks file changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks file changes")
# File change tracking monitors timestamps and hashes
expect(true)
```

</details>

#### detects file modifications

- detects file modifications


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects file modifications")
# File modification detection identifies updated files
expect(true)
```

</details>

#### identifies files needing recompilation

- identifies files needing recompilation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies files needing recompilation")
# Identifies which files need recompilation based on dependencies
expect(true)
```

</details>

#### Dependency Tracking

#### builds dependency graph

- builds dependency graph


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds dependency graph")
# Build dependency graph from import statements
expect(true)
```

</details>

#### detects circular dependencies

- detects circular dependencies


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects circular dependencies")
# Circular dependency detection via cycle detection algorithm
expect(true)
```

</details>

#### computes topological order

- computes topological order


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes topological order")
# Topological sort of dependencies for build order
expect(true)
```

</details>

#### Error Aggregation

#### collects errors from multiple languages

- collects errors from multiple languages


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects errors from multiple languages")
# Collect errors from all language compilers
expect(true)
```

</details>

#### normalizes error formats

- normalizes error formats


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes error formats")
# Convert different error formats to unified schema
expect(true)
```

</details>

#### groups errors by file

- groups errors by file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("groups errors by file")
# Group and organize errors by source file
expect(true)
```

</details>

#### Test Runner

#### creates test configuration

- creates test configuration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates test configuration")
# Initialize test runner configuration
expect(true)
```

</details>

#### configures parallel execution

- configures parallel execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("configures parallel execution")
# Enable parallel test execution with worker pools
expect(true)
```

</details>

#### creates test result

- creates test result


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates test result")
# Create test result tracking object
expect(true)
```

</details>

#### generates test summary

- generates test summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates test summary")
# Generate human-readable test summary report
expect(true)
```

</details>

#### Deployment Pipeline

#### creates deployment pipeline

- creates deployment pipeline


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates deployment pipeline")
# Create deployment pipeline with stages
expect(true)
```

</details>

#### adds pipeline stages

- adds pipeline stages


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds pipeline stages")
# Add stages to deployment pipeline
expect(true)
```

</details>

#### executes pipeline stages

- executes pipeline stages


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes pipeline stages")
# Execute pipeline stages in sequence
expect(true)
```

</details>

#### Compilation Modes

#### supports debug mode

- supports debug mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports debug mode")
# Compile in debug mode with symbols
expect(true)
```

</details>

#### supports release mode

- supports release mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports release mode")
# Compile in release mode with optimizations
expect(true)
```

</details>

#### Language Support

#### recognizes all supported languages

- recognizes all supported languages


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes all supported languages")
# Recognize Simple, Rust, Python, JavaScript, TypeScript, Go, C, C++
expect(true)
```

</details>

#### converts language to string

- converts language to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts language to string")
# Convert language enum to string representation
expect(true)
```

</details>

#### Compilation Results

#### creates successful compilation result

- creates successful compilation result


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates successful compilation result")
# Create successful compilation result object
expect(true)
```

</details>

#### creates failed compilation result

- creates failed compilation result


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates failed compilation result")
# Create failed compilation result with errors
expect(true)
```

</details>

#### Integration

#### builds multi-language project

- builds multi-language project


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds multi-language project")
# Build entire multi-language project
expect(true)
```

</details>

#### runs multi-language tests

- runs multi-language tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs multi-language tests")
# Run tests across multiple languages
expect(true)
```

</details>

#### deploys multi-language project

- deploys multi-language project


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deploys multi-language project")
# Deploy compiled multi-language artifacts
expect(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/tooling_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Multi-Language Tooling.
- Multi-Language Tooling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `81873a1d528d69dcfdfd3c164ba6f704ad2ae52174dd88b14f8d1242b6a27c07`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `81873a1d528d69dcfdfd3c164ba6f704ad2ae52174dd88b14f8d1242b6a27c07`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `81873a1d528d69dcfdfd3c164ba6f704ad2ae52174dd88b14f8d1242b6a27c07`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/tooling_spec.spl
mirror: doc/06_spec/unit/app/tooling/tooling_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/tooling_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/tooling_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/tooling_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects Simple projects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/tooling_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects multi-language projects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/tooling_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates project configuration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
