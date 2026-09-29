# Dynamic Versioned Specification

> Tests covering LibVersion, build_candidate_paths, library_search_paths.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dynamic Versioned Specification

## Scenarios

### LibVersion

#### formats any version

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- formats any version
   - Expected: lib_version_string(v) equals `any`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats any version")
val v = lib_version_any()
expect(lib_version_string(v)).to_equal("any")
```

</details>

#### formats major only

- formats major only
   - Expected: lib_version_string(v) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats major only")
val v = lib_version(1, 0, 0)
expect(lib_version_string(v)).to_equal("1")
```

</details>

#### formats major.minor

- formats major.minor
   - Expected: lib_version_string(v) equals `2.3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats major.minor")
val v = lib_version(2, 3, 0)
expect(lib_version_string(v)).to_equal("2.3")
```

</details>

#### formats major.minor.patch

- formats major.minor.patch
   - Expected: lib_version_string(v) equals `1.2.3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats major.minor.patch")
val v = lib_version(1, 2, 3)
expect(lib_version_string(v)).to_equal("1.2.3")
```

</details>

### build_candidate_paths

#### generates candidates for unversioned library

- generates candidates for unversioned library
   - Expected: paths.len() > 0 is true
   - Expected: has_lib_prefix is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates candidates for unversioned library")
val paths = build_candidate_paths("t32api64", lib_version_any())
# Should contain at least bare name fallback
expect(paths.len() > 0).to_equal(true)
# Should contain lib prefix variant
var has_lib_prefix = false
var i = 0
while i < paths.len():
    if paths[i].contains("libt32api64"):
        has_lib_prefix = true
    i = i + 1
expect(has_lib_prefix).to_equal(true)
```

</details>

#### generates versioned candidates

- generates versioned candidates
   - Expected: has_major_version is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates versioned candidates")
val paths = build_candidate_paths("mylib", lib_version(2, 1, 0))
# Should contain versioned .so.2 or .2.dylib variants
var has_major_version = false
var i = 0
while i < paths.len():
    if paths[i].contains(".2") or paths[i].contains("so.2"):
        has_major_version = true
    i = i + 1
expect(has_major_version).to_equal(true)
```

</details>

#### generates full version candidates

- generates full version candidates
   - Expected: has_full_version is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates full version candidates")
val paths = build_candidate_paths("mylib", lib_version(1, 2, 3))
var has_full_version = false
var i = 0
while i < paths.len():
    if paths[i].contains("1.2.3"):
        has_full_version = true
    i = i + 1
expect(has_full_version).to_equal(true)
```

</details>

### library_search_paths

#### returns at least one search path

- returns at least one search path
   - Expected: paths.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns at least one search path")
val paths = library_search_paths()
expect(paths.len() > 0).to_equal(true)
```

</details>

#### includes T32 API path

- includes T32 API path
   - Expected: has_t32 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes T32 API path")
val paths = library_search_paths()
var has_t32 = false
var i = 0
while i < paths.len():
    if paths[i].contains("t32"):
        has_t32 = true
    i = i + 1
expect(has_t32).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/ffi/dynamic_versioned_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LibVersion, build_candidate_paths, library_search_paths.
- LibVersion
- build_candidate_paths
- library_search_paths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `c4ee499a14f2bd21f94118ae336b61613a82a72abb5e0ee5378eaa7c8268eae7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c4ee499a14f2bd21f94118ae336b61613a82a72abb5e0ee5378eaa7c8268eae7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c4ee499a14f2bd21f94118ae336b61613a82a72abb5e0ee5378eaa7c8268eae7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/ffi/dynamic_versioned_spec.spl
mirror: doc/06_spec/unit/lib/ffi/dynamic_versioned_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/ffi/dynamic_versioned_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/ffi/dynamic_versioned_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/ffi/dynamic_versioned_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats any version' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/ffi/dynamic_versioned_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats major only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/ffi/dynamic_versioned_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats major.minor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
