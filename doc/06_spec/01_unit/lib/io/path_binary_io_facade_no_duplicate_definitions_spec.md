# Path Binary Io Facade No Duplicate Definitions Specification

> Tests covering nogc_async_mut path/binary_io facades stay definition-free.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Path Binary Io Facade No Duplicate Definitions Specification

## Scenarios

### nogc_async_mut path/binary_io facades stay definition-free

#### path facade re-exports the canonical implementation (behavioral wire-through)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### path facade contains zero local definitions - only export use

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: no duplicate-named fn bodies may re-grow in the path facade
val src = file_read(path_facade)
expect src.len() > 0
val hits = local_definition_lines(src)
if hits.len() > 0:
    print "path facade regrew local definitions (Class B collision risk):"
    for h in hits:
        print "  {h}"
expect hits.len() == 0
expect src.contains("export use std.nogc_sync_mut.path.") == true
```

</details>

#### binary_io facade contains zero local definitions - only export use

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: no duplicate fn/class bodies may re-grow in the binary_io facade
val src = file_read(binio_facade)
expect src.len() > 0
val hits = local_definition_lines(src)
if hits.len() > 0:
    print "binary_io facade regrew local definitions (Class B collision risk):"
    for h in hits:
        print "  {h}"
expect hits.len() == 0
expect src.contains("export use std.common.binary_io.") == true
```

</details>

#### scan control: canonical binary_io still has real definitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: absence check paired with a control that MUST hit
val src = file_read("src/lib/common/binary_io.spl")
val hits = local_definition_lines(src)
expect hits.len() > 10
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/io/path_binary_io_facade_no_duplicate_definitions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut path/binary_io facades stay definition-free.
- nogc_async_mut path/binary_io facades stay definition-free

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6f3622b1d0a5012518ec272cd6eba96080cc7830979ec32594b02da0bdff8272`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6f3622b1d0a5012518ec272cd6eba96080cc7830979ec32594b02da0bdff8272`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6f3622b1d0a5012518ec272cd6eba96080cc7830979ec32594b02da0bdff8272`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/lib/io/path_binary_io_facade_no_duplicate_definitions_spec.spl
mirror: doc/06_spec/01_unit/lib/io/path_binary_io_facade_no_duplicate_definitions_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/io/path_binary_io_facade_no_duplicate_definitions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/io/path_binary_io_facade_no_duplicate_definitions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/io/path_binary_io_facade_no_duplicate_definitions_spec.spl:41:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'path facade re-exports the canonical implementation (behavioral wire-through)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/io/path_binary_io_facade_no_duplicate_definitions_spec.spl:50:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'path facade contains zero local definitions - only export use' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/io/path_binary_io_facade_no_duplicate_definitions_spec.spl:62:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'binary_io facade contains zero local definitions - only export use' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/io/path_binary_io_facade_no_duplicate_definitions_spec.spl:74:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'scan control: canonical binary_io still has real definitions' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
