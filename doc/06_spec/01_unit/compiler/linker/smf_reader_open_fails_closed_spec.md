# `SmfReaderFfi.open` must fail closed on a path that does not exist

> `rt_smf_reader_open` is an unregistered extern -- there is no implementation anywhere in the tree. An unregistered extern does not fail to link; it yields a silent `0`. The guard in `SmfReaderFfi.open` was `handle < 0`, which `0` does not satisfy, so `open()` returned `Ok` for EVERY path, including one that does not exist, and every subsequent read handed back empty data.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `SmfReaderFfi.open` must fail closed on a path that does not exist

`rt_smf_reader_open` is an unregistered extern -- there is no implementation anywhere in the tree. An unregistered extern does not fail to link; it yields a silent `0`. The guard in `SmfReaderFfi.open` was `handle < 0`, which `0` does not satisfy, so `open()` returned `Ok` for EVERY path, including one that does not exist, and every subsequent read handed back empty data.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Linker / SMF reader (reproducer) |
| Status | Active |
| Source | `test/01_unit/compiler/linker/smf_reader_open_fails_closed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`rt_smf_reader_open` is an unregistered extern -- there is no implementation
anywhere in the tree. An unregistered extern does not fail to link; it yields a
silent `0`. The guard in `SmfReaderFfi.open` was `handle < 0`, which `0` does
not satisfy, so `open()` returned `Ok` for EVERY path, including one that does
not exist, and every subsequent read handed back empty data.

The observable consequence: a missing input object and an empty one were
indistinguishable. This spec pins the missing-file case as an `Err`.

## Why this spec does not need a subprocess

Unlike the MIR/native-codegen bugs in this cluster, the defect here is in
library control flow (a guard that could never be true), not in code
generation. It is equally present interpreted, so an in-process example has
teeth. The `SIMPLE_BOOTSTRAP`-style native round trip would add ten minutes and
prove nothing extra.

## Scenarios

### SmfReaderFfi.open on a nonexistent path

#### reports Err rather than a usable-looking reader

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports Err rather than a usable-looking reader
- Open a path that certainly does not exist
- The result is Err, not a silently-empty Ok
   - Expected: "open() returned Ok for a nonexistent path" equals `Err`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports Err rather than a usable-looking reader")
step("Open a path that certainly does not exist")
val missing = "build/test-artifacts/definitely-not-here-smf_reader_spec.smf"
val opened = SmfReaderFfi.open(missing)

step("The result is Err, not a silently-empty Ok")
match opened:
    case Err(msg):
        expect(msg).to_contain("no such file")
        expect(msg).to_contain("definitely-not-here")
    case Ok(_):
        # Under the defect this arm is taken and the reader then
        # answers every read with empty data under exit 0.
        expect("open() returned Ok for a nonexistent path").to_equal("Err")
```

</details>

#### does not treat the empty path as openable either

- does not treat the empty path as openable either
- The empty string is not a file


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat the empty path as openable either")
step("The empty string is not a file")
match SmfReaderFfi.open(""):
    case Err(_): expect(true).to_equal(true)
    case Ok(_): expect("open(\"\") returned Ok").to_equal("Err")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `2527a6c43da6e9cbf40661056aa045fbd23ee6e6e2ded2bf0228ea0d813dbbb6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2527a6c43da6e9cbf40661056aa045fbd23ee6e6e2ded2bf0228ea0d813dbbb6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2527a6c43da6e9cbf40661056aa045fbd23ee6e6e2ded2bf0228ea0d813dbbb6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/compiler/linker/smf_reader_open_fails_closed_spec.spl
mirror: doc/06_spec/01_unit/compiler/linker/smf_reader_open_fails_closed_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/linker/smf_reader_open_fails_closed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/linker/smf_reader_open_fails_closed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/linker/smf_reader_open_fails_closed_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports Err rather than a usable-looking reader' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/smf_reader_open_fails_closed_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not treat the empty path as openable either' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
