# Discovery Specification

> Tests covering DiscoveryConfig, File Discovery, Pattern Matching, Full Discovery.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Discovery Specification

## Scenarios

### DiscoveryConfig

#### default configuration

#### has default search paths

- has default search paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("has default search paths")
val config = DiscoveryConfig.default()
expect config.get_search_paths().len() to_be 3
expect config.has_search_path("lib/") to_be true
expect config.has_search_path("src/") to_be true
expect config.has_search_path("doc/") to_be true
```

</details>

#### has default include patterns

- has default include patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("has default include patterns")
val config = DiscoveryConfig.default()
val patterns = config.get_include_patterns()
expect patterns.len() to_be 3
```

</details>

#### has default exclude patterns

- has default exclude patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("has default exclude patterns")
val config = DiscoveryConfig.default()
val patterns = config.get_exclude_patterns()
expect patterns.len() to_be 2
```

</details>

#### configuration modification

#### adds search path

- adds search path


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("adds search path")
val config = DiscoveryConfig.default()
    .add_search_path("tests/")
expect config.has_search_path("tests/") to_be true
expect config.get_search_paths().len() to_be 4
```

</details>

#### adds include pattern

- adds include pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("adds include pattern")
val config = DiscoveryConfig.default()
    .add_include_pattern("**/*.rst")
val patterns = config.get_include_patterns()
expect patterns.len() to_be 4
```

</details>

#### adds exclude pattern

- adds exclude pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("adds exclude pattern")
val config = DiscoveryConfig.default()
    .add_exclude_pattern("**/cache/**")
val patterns = config.get_exclude_patterns()
expect patterns.len() to_be 3
```

</details>

#### summary

#### provides configuration summary

- provides configuration summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("provides configuration summary")
val config = DiscoveryConfig.default()
val summary = config.summary()
expect summary.contains("search paths") to_be true
expect summary.contains("include patterns") to_be true
expect summary.contains("exclude patterns") to_be true
```

</details>

### File Discovery

#### discover_file function

#### returns empty list for unknown extensions

- returns empty list for unknown extensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns empty list for unknown extensions")
val found = discover_file("unknown.xyz")
expect found.len() to_be 0
```

</details>

#### recognizes spl files

- recognizes spl files


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("recognizes spl files")
val found = discover_file("test.spl")
expect found.is_list() to_be true
```

</details>

#### recognizes md files

- recognizes md files


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("recognizes md files")
val found = discover_file("test.md")
expect found.is_list() to_be true
```

</details>

### Pattern Matching

#### should_exclude function

#### excludes paths matching target pattern

- excludes paths matching target pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("excludes paths matching target pattern")
val exclude_patterns = ["**/target/**"]
expect should_exclude("project/target/debug/test.spl", exclude_patterns) to_be true
```

</details>

#### does not exclude non-matching paths

- does not exclude non-matching paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("does not exclude non-matching paths")
val exclude_patterns = ["**/target/**", "**/build/**"]
expect should_exclude("src/lib/module.spl", exclude_patterns) to_be false
```

</details>

#### matches_any_pattern function

#### matches spl files

- matches spl files


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches spl files")
val include_patterns = ["**/*.spl"]
expect matches_any_pattern("src/module.spl", include_patterns) to_be true
```

</details>

#### does not match non-matching extensions

- does not match non-matching extensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("does not match non-matching extensions")
val include_patterns = ["**/*.spl"]
expect matches_any_pattern("src/module.rs", include_patterns) to_be false
```

</details>

### Full Discovery

#### discover_all function

#### returns a list

- returns a list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns a list")
val config = DiscoveryConfig.default()
val found = discover_all(config)
expect found.is_list() to_be true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/integration/lib/std/doctest/discovery_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DiscoveryConfig, File Discovery, Pattern Matching, Full Discovery.
- DiscoveryConfig
- File Discovery
- Pattern Matching
- Full Discovery

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `06f0791e94210974a2fee0d9192f29fc69fbed0896fbb7d7f93996e0b774a810`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `06f0791e94210974a2fee0d9192f29fc69fbed0896fbb7d7f93996e0b774a810`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `06f0791e94210974a2fee0d9192f29fc69fbed0896fbb7d7f93996e0b774a810`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/lib/std/doctest/discovery_spec.spl
mirror: doc/06_spec/integration/lib/std/doctest/discovery_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/lib/std/doctest/discovery_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/lib/std/doctest/discovery_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/lib/std/doctest/discovery_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has default search paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/std/doctest/discovery_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has default include patterns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/std/doctest/discovery_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has default exclude patterns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
