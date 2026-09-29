# Block Scoped Use Resolves Specification

> Tests covering block-scoped use resolves imported functions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Block Scoped Use Resolves Specification

## Scenarios

### block-scoped use resolves imported functions

#### resolves a function imported inside a function body

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves a function imported inside a function body
- Call a function whose only import is body-scoped


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves a function imported inside a function body")
"""A `use` in a function body must bring the named function into scope,
exactly as the same import written at module scope does."""

step("Call a function whose only import is body-scoped")
# rotr32 is imported inside this function body, not at module scope.
use std.crypto.types.{rotr32}
expect(rotr32(16, 4)).to_be(1)
```

</details>

#### runs a stdlib function that relies on body-scoped imports

- runs a stdlib function that relies on body-scoped imports
- Hash a known input and compare against the published SHA-1 vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("runs a stdlib function that relies on body-scoped imports")
"""std.crypto.sha1.sha1_hex imports text_to_bytes and bytes_to_hex in
its own function body. Before the fix this raised E1002 for
bytes_to_hex, making the shipped function unusable."""

step("Hash a known input and compare against the published SHA-1 vector")
# FIPS 180-1 test vector: SHA-1("abc").
expect(sha1_hex("abc")).to_be("a9993e364706816aba3e25717850c26c9cd0d89d")
```

</details>

#### binds an aliased body-scoped import under its alias

- binds an aliased body-scoped import under its alias
- Import under an alias inside the body and call through it


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds an aliased body-scoped import under its alias")
"""The Group-with-alias form must bind the alias, not the original
name -- the same rule module scope applies."""

step("Import under an alias inside the body and call through it")
use std.crypto.types.{rotr32 as rotate_right}
expect(rotate_right(16, 4)).to_be(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/block_scoped_use_resolves_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering block-scoped use resolves imported functions.
- block-scoped use resolves imported functions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `431de31b10a4f299be340b402b618e234249e7321657757452a546734ba4f722`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `431de31b10a4f299be340b402b618e234249e7321657757452a546734ba4f722`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `431de31b10a4f299be340b402b618e234249e7321657757452a546734ba4f722`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interpreter/block_scoped_use_resolves_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/block_scoped_use_resolves_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/block_scoped_use_resolves_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/block_scoped_use_resolves_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/block_scoped_use_resolves_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a function imported inside a function body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/block_scoped_use_resolves_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs a stdlib function that relies on body-scoped imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/block_scoped_use_resolves_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds an aliased body-scoped import under its alias' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
