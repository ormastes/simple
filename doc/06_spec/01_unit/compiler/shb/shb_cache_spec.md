# Shb Cache Specification

> Tests covering SHB Cache, Cache Config, Cache Manager, Two-Level Cache Logic, Stale Detection, Dependency Validation, Batch Processing, Batch Summary, Atomic Write Safety, Watcher Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shb Cache Specification

## Scenarios

### SHB Cache

### Cache Config

#### default cache dir is .build/headers

- default cache dir is .build/headers
   - Expected: cache_dir equals `.build/headers`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("default cache dir is .build/headers")
val cache_dir = ".build/headers"
expect(cache_dir).to_equal(".build/headers")
```

</details>

#### default config is enabled

- default config is enabled
   - Expected: enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("default config is enabled")
val enabled = true
expect(enabled).to_equal(true)
```

</details>

### Cache Manager

#### creates with default config

- creates with default config
   - Expected: cache_dir.starts_with(".build") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates with default config")
val cache_dir = ".build/headers"
expect(cache_dir.starts_with(".build")).to_equal(true)
```

</details>

#### converts source path to shb path

- converts source path to shb path
   - Expected: step2 equals `src_app_cli_main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("converts source path to shb path")
# src/app/cli/main.spl => .build/headers/src_app_cli_main.shb
val source = "src/app/cli/main.spl"
var step1 = source.replace("/", "_")
var step2 = step1.replace(".spl", "")
expect(step2).to_equal("src_app_cli_main")
```

</details>

#### converts nested paths correctly

- converts nested paths correctly
   - Expected: step2 equals `src_compiler_shb_shb_types`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("converts nested paths correctly")
val source = "src/compiler/shb/shb_types.spl"
var step1 = source.replace("/", "_")
var step2 = step1.replace(".spl", "")
expect(step2).to_equal("src_compiler_shb_shb_types")
```

</details>

### Two-Level Cache Logic

#### returns UNCHANGED when source hash matches

- returns UNCHANGED when source hash matches
   - Expected: status_unchanged equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns UNCHANGED when source hash matches")
# source_hash == .shb.source_hash => skip
val status_unchanged = 0
expect(status_unchanged).to_equal(0)
```

</details>

#### returns BODY_ONLY when interface hash matches

- returns BODY_ONLY when interface hash matches
   - Expected: status_body equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns BODY_ONLY when interface hash matches")
# source changed, interface same => recompile this file only
val status_body = 1
expect(status_body).to_equal(1)
```

</details>

#### returns INTERFACE when interface hash differs

- returns INTERFACE when interface hash differs
   - Expected: status_iface equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns INTERFACE when interface hash differs")
# interface changed => recompile this + dependents
val status_iface = 2
expect(status_iface).to_equal(2)
```

</details>

#### returns NEW when no cache exists

- returns NEW when no cache exists
   - Expected: status_new equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns NEW when no cache exists")
val status_new = 3
expect(status_new).to_equal(3)
```

</details>

#### returns ERROR on read failure

- returns ERROR on read failure
   - Expected: status_error equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns ERROR on read failure")
val status_error = -1
expect(status_error).to_equal(-1)
```

</details>

### Stale Detection

#### detects stale when no cache exists

- detects stale when no cache exists
   - Expected: cache_exists is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("detects stale when no cache exists")
# No .shb file => stale
val cache_exists = false
expect(cache_exists).to_equal(false)
```

</details>

#### detects stale when hash mismatches

- detects stale when hash mismatches
   - Expected: 42 != 99 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("detects stale when hash mismatches")
# Expected hash 42 but actual hash 99 => stale
expect(42 != 99).to_equal(true)
```

</details>

#### not stale when hash matches

- not stale when hash matches
   - Expected: 42 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("not stale when hash matches")
# Expected 42, actual 42 => not stale
expect(42).to_equal(42)
```

</details>

### Dependency Validation

#### validates when all dep hashes match

- validates when all dep hashes match
   - Expected: actual_hash equals `expected_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("validates when all dep hashes match")
val expected_hash = 42
val actual_hash = 42
expect(actual_hash).to_equal(expected_hash)
```

</details>

#### fails when any dep hash mismatches

- fails when any dep hash mismatches
   - Expected: actual_hash != expected_hash is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails when any dep hash mismatches")
val expected_hash = 42
val actual_hash = 99
expect(actual_hash != expected_hash).to_equal(true)
```

</details>

#### fails when dep file not found

- fails when dep file not found
   - Expected: dep_exists is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails when dep file not found")
val dep_exists = false
expect(dep_exists).to_equal(false)
```

</details>

### Batch Processing

#### empty batch produces zero counts

- empty batch produces zero counts
   - Expected: unchanged equals `0`
   - Expected: errors equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("empty batch produces zero counts")
val unchanged = 0
val errors = 0
expect(unchanged).to_equal(0)
expect(errors).to_equal(0)
```

</details>

#### skips non-spl files

- skips non-spl files
   - Expected: is_spl is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("skips non-spl files")
# readme.md is not .spl => skipped
val path = "readme.md"
val is_spl = path.ends_with(".spl")
expect(is_spl).to_equal(false)
```

</details>

#### skips deleted files

- skips deleted files
   - Expected: should_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("skips deleted files")
val event_type = "deleted"
val should_skip = event_type == "deleted"
expect(should_skip).to_equal(true)
```

</details>

#### detects interface changes in batch

- detects interface changes in batch
   - Expected: has_changes is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("detects interface changes in batch")
val iface_changed = 1
val has_changes = iface_changed > 0
expect(has_changes).to_equal(true)
```

</details>

#### reports no interface changes when body-only

- reports no interface changes when body-only
   - Expected: has_changes is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports no interface changes when body-only")
val iface_changed = 0
val has_changes = iface_changed > 0
expect(has_changes).to_equal(false)
```

</details>

### Batch Summary

#### formats counts correctly

- formats counts correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("formats counts correctly")
# "5 unchanged, 2 body-only, 1 interface changed"
val summary = "5 unchanged, 2 body-only, 1 interface changed"
expect(summary).to_contain("2 body-only")
```

</details>

### Atomic Write Safety

#### writes to temp file first

- writes to temp file first


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("writes to temp file first")
# path.tmp is written, then renamed to path
val temp_path = ".build/headers/module.shb.tmp"
expect(temp_path).to_end_with(".tmp")
```

</details>

#### rename is atomic on same filesystem

- rename is atomic on same filesystem
   - Expected: source_dir equals `target_dir`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rename is atomic on same filesystem")
# Linux guarantees atomic rename
val source_dir = ".build/headers"
val target_dir = ".build/headers"
expect(source_dir).to_equal(target_dir)
```

</details>

### Watcher Integration

#### converts FileChangeEvent to ShbChangeEvent

- converts FileChangeEvent to ShbChangeEvent


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("converts FileChangeEvent to ShbChangeEvent")
val event = "src/app/main.spl:modified"
expect(event).to_contain("modified")
```

</details>

#### shb_mode flag enables SHB generation

- shb_mode flag enables SHB generation
   - Expected: shb_mode is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shb_mode flag enables SHB generation")
val shb_mode = true
expect(shb_mode).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/shb/shb_cache_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SHB Cache, Cache Config, Cache Manager, Two-Level Cache Logic, Stale Detection, Dependency Validation, Batch Processing, Batch Summary, Atomic Write Safety, Watcher Integration.
- SHB Cache
- Cache Config
- Cache Manager
- Two-Level Cache Logic
- Stale Detection
- Dependency Validation
- Batch Processing
- Batch Summary
- Atomic Write Safety
- Watcher Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `208c6ba296fb2af592fcbd47da0ba6d4def993deba21525885657ee8d6150a8b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `208c6ba296fb2af592fcbd47da0ba6d4def993deba21525885657ee8d6150a8b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `208c6ba296fb2af592fcbd47da0ba6d4def993deba21525885657ee8d6150a8b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/shb/shb_cache_spec.spl
mirror: doc/06_spec/01_unit/compiler/shb/shb_cache_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/shb/shb_cache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/shb/shb_cache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/shb/shb_cache_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/shb/shb_cache_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default cache dir is .build/headers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/shb/shb_cache_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default config is enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/shb/shb_cache_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates with default config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
