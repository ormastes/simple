# Audio Ffi Specification

> Tests covering audio FFI compatibility facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Audio Ffi Specification

## Scenarios

### audio FFI compatibility facade

#### keeps the app SFFI path as a safe facade over the no-GC owner

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the app SFFI path as a safe facade over the no-GC owner
   - Expected: source does not contain `extern fn `
   - Expected: source does not contain `rt_audio_`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the app SFFI path as a safe facade over the no-GC owner")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = file_read("src/app/io/audio_sffi.spl")
expect(source.contains("extern fn ")).to_equal(false)
expect(source).to_contain("std.nogc_sync_mut.io.audio_sffi.{{")
expect(source.contains("rt_audio_")).to_equal(false)
```

</details>

#### contains no duplicate foreign declarations

- contains no duplicate foreign declarations
   - Expected: source does not contain `extern fn `
   - Expected: source does not contain `@extern(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("contains no duplicate foreign declarations")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = file_read("src/app/io/audio_ffi.spl")
expect(source.contains("extern fn ")).to_equal(false)
expect(source.contains("@extern(")).to_equal(false)
```

</details>

#### exports the canonical safe audio surface explicitly

- exports the canonical safe audio surface explicitly
   - Expected: source contains `audio_init`
   - Expected: source contains `audio_capture_stop`
   - Expected: source does not contain `audio_sffi.*`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exports the canonical safe audio surface explicitly")
val source = file_read("src/app/io/audio_ffi.spl")
expect(source).to_contain("export use app.io.audio_sffi.{{")
expect(source.contains("audio_init")).to_equal(true)
expect(source.contains("audio_capture_stop")).to_equal(true)
expect(source.contains("audio_sffi.*")).to_equal(false)
```

</details>

#### does not re-export raw runtime symbols

- does not re-export raw runtime symbols
   - Expected: source does not contain `rt_audio_`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not re-export raw runtime symbols")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = file_read("src/app/io/audio_ffi.spl")
expect(source.contains("rt_audio_")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/audio_ffi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering audio FFI compatibility facade.
- audio FFI compatibility facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ca5ba21e5c3a04ceb28f910be50e885f9b6c44b9224406d0f82616e657c9e42a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca5ba21e5c3a04ceb28f910be50e885f9b6c44b9224406d0f82616e657c9e42a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca5ba21e5c3a04ceb28f910be50e885f9b6c44b9224406d0f82616e657c9e42a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/io/audio_ffi_spec.spl
mirror: doc/06_spec/01_unit/app/io/audio_ffi_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/01_unit/app/io/audio_ffi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/io/audio_ffi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/io/audio_ffi_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
<!-- sspec-maintain:scorecard:end -->
