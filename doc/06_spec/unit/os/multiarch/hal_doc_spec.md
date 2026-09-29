# Hal Doc Specification

> Tests covering AC-7 — multi-arch HAL architecture doc exists, AC-7 — doc names every locked trait, AC-7 — doc contains the hardening matrix and six-arch contract, AC-7 — doc is linked from mdsoc_architecture_tobe.md, AC-7 — doc records test results table.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hal Doc Specification

## Scenarios

### AC-7 — multi-arch HAL architecture doc exists

#### doc file exists

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- doc file exists
   - Expected: file_exists(ARCH_DOC) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("doc file exists")
expect(file_exists(ARCH_DOC)).to_equal(true)
```

</details>

#### doc is non-empty

- doc is non-empty
   - Expected: body.length() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("doc is non-empty")
val body: text = file_read(ARCH_DOC)
expect(body.length() > 0).to_equal(true)
```

</details>

#### doc declares the 16-trait surface as LOCKED

- doc declares the 16-trait surface as LOCKED
   - Expected: body contains `HAL Trait Surface`
   - Expected: body contains `16 traits`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("doc declares the 16-trait surface as LOCKED")
val body: text = file_read(ARCH_DOC)
expect(body.contains("HAL Trait Surface")).to_equal(true)
expect(body.contains("16 traits")).to_equal(true)
```

</details>

### AC-7 — doc names every locked trait

#### names HalConsole

- names HalConsole
   - Expected: b contains `HalConsole`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names HalConsole")
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalConsole")).to_equal(true)
```

</details>

#### names HalBoot

- names HalBoot
   - Expected: b contains `HalBoot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names HalBoot")
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalBoot")).to_equal(true)
```

</details>

#### names HalCpu

- names HalCpu
   - Expected: b contains `HalCpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names HalCpu")
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalCpu")).to_equal(true)
```

</details>

#### names HalPower

- names HalPower
   - Expected: b contains `HalPower`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names HalPower")
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalPower")).to_equal(true)
```

</details>

#### names HalPaging

- names HalPaging
   - Expected: b contains `HalPaging`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names HalPaging")
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalPaging")).to_equal(true)
```

</details>

#### names HalInterrupt

- names HalInterrupt
   - Expected: b contains `HalInterrupt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names HalInterrupt")
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalInterrupt")).to_equal(true)
```

</details>

#### names HalTimer

- names HalTimer
   - Expected: b contains `HalTimer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names HalTimer")
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalTimer")).to_equal(true)
```

</details>

#### names HalContext

- names HalContext
   - Expected: b contains `HalContext`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names HalContext")
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalContext")).to_equal(true)
```

</details>

#### names HalEntropy

- names HalEntropy
   - Expected: b contains `HalEntropy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names HalEntropy")
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalEntropy")).to_equal(true)
```

</details>

#### names HalCstart

- names HalCstart
   - Expected: b contains `HalCstart`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names HalCstart")
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalCstart")).to_equal(true)
```

</details>

#### names HalSyscall

- names HalSyscall
   - Expected: b contains `HalSyscall`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names HalSyscall")
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalSyscall")).to_equal(true)
```

</details>

#### names HalCanary

- names HalCanary
   - Expected: b contains `HalCanary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names HalCanary")
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalCanary")).to_equal(true)
```

</details>

#### names HalBarrier

- names HalBarrier
   - Expected: b contains `HalBarrier`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names HalBarrier")
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalBarrier")).to_equal(true)
```

</details>

#### names HalCache

- names HalCache
   - Expected: b contains `HalCache`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names HalCache")
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalCache")).to_equal(true)
```

</details>

#### names HalSmp

- names HalSmp
   - Expected: b contains `HalSmp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names HalSmp")
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalSmp")).to_equal(true)
```

</details>

#### names HalPerCpu

- names HalPerCpu
   - Expected: b contains `HalPerCpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names HalPerCpu")
val b: text = file_read(ARCH_DOC)
expect(b.contains("HalPerCpu")).to_equal(true)
```

</details>

### AC-7 — doc contains the hardening matrix and six-arch contract

<details>
<summary>Advanced: documents the hardening matrix</summary>

#### documents the hardening matrix

- documents the hardening matrix
   - Expected: b contains `Hardening Matrix`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents the hardening matrix")
val b: text = file_read(ARCH_DOC)
expect(b.contains("Hardening Matrix")).to_equal(true)
```

</details>


</details>

#### lists all six architecture triples

- lists all six architecture triples
   - Expected: b contains `x86_64`
   - Expected: b contains `x86_32`
   - Expected: b contains `"aarch64") or b`
   - Expected: b contains `"armv7") or b`
   - Expected: b contains `"riscv64") or b`
   - Expected: b contains `"riscv32") or b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists all six architecture triples")
val b: text = file_read(ARCH_DOC)
expect(b.contains("x86_64")).to_equal(true)
expect(b.contains("x86_32")).to_equal(true)
expect(b.contains("aarch64") or b.contains("arm64")).to_equal(true)
expect(b.contains("armv7") or b.contains("arm32")).to_equal(true)
expect(b.contains("riscv64") or b.contains("rv64gc")).to_equal(true)
expect(b.contains("riscv32") or b.contains("rv32imac")).to_equal(true)
```

</details>

#### documents the AC-3 LoC floor rationale (40% / 25% fallback)

- documents the AC-3 LoC floor rationale (40% / 25% fallback)
   - Expected: ok is true
   - Expected: fallback_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents the AC-3 LoC floor rationale (40% / 25% fallback)")
val b: text = file_read(ARCH_DOC)
val ok: bool = b.contains("40%") or b.contains("≥40")
expect(ok).to_equal(true)
val fallback_ok: bool = b.contains("25%") or b.contains("walker")
expect(fallback_ok).to_equal(true)
```

</details>

### AC-7 — doc is linked from mdsoc_architecture_tobe.md

#### mdsoc tobe doc exists

- mdsoc tobe doc exists
   - Expected: file_exists(MDSOC_DOC) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mdsoc tobe doc exists")
expect(file_exists(MDSOC_DOC)).to_equal(true)
```

</details>

#### mdsoc tobe doc references simpleos_multiarch_hal

- mdsoc tobe doc references simpleos_multiarch_hal
   - Expected: b contains `simpleos_multiarch_hal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mdsoc tobe doc references simpleos_multiarch_hal")
val b: text = file_read(MDSOC_DOC)
expect(b.contains("simpleos_multiarch_hal")).to_equal(true)
```

</details>

### AC-7 — doc records test results table
_The doc must summarise the verification status of each AC._

#### doc contains a Test Results section

- doc contains a Test Results section
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("doc contains a Test Results section")
val b: text = file_read(ARCH_DOC)
val ok: bool = b.contains("Test Results") or b.contains("Verification")
expect(ok).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/multiarch/hal_doc_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AC-7 — multi-arch HAL architecture doc exists, AC-7 — doc names every locked trait, AC-7 — doc contains the hardening matrix and six-arch contract, AC-7 — doc is linked from mdsoc_architecture_tobe.md, AC-7 — doc records test results table.
- AC-7 — multi-arch HAL architecture doc exists
- AC-7 — doc names every locked trait
- AC-7 — doc contains the hardening matrix and six-arch contract
- AC-7 — doc is linked from mdsoc_architecture_tobe.md
- AC-7 — doc records test results table

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
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

- Canonical SPipe generation for source `24a7eacbbf9cb0600175c4bee0e1d121d92cc4b170dd66e0ff11ceccc037f999`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `24a7eacbbf9cb0600175c4bee0e1d121d92cc4b170dd66e0ff11ceccc037f999`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `24a7eacbbf9cb0600175c4bee0e1d121d92cc4b170dd66e0ff11ceccc037f999`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/multiarch/hal_doc_spec.spl
mirror: doc/06_spec/unit/os/multiarch/hal_doc_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/multiarch/hal_doc_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/multiarch/hal_doc_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/multiarch/hal_doc_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'doc file exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/multiarch/hal_doc_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'doc is non-empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/multiarch/hal_doc_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'doc declares the 16-trait surface as LOCKED' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
