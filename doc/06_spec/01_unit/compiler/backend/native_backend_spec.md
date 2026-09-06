# Native Backend Specification

> Tests covering Native Backend.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Backend Specification

## Scenarios

### Native Backend

#### keeps ELF byte-buffer primitives available

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps ELF byte-buffer primitives available


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps ELF byte-buffer primitives available")
val source = read_native_source("src/compiler/70.backend/backend/native/elf_writer.spl")

expect(source).to_contain("struct ByteBuffer")
expect(source).to_contain("fn new_byte_buffer() -> ByteBuffer")
```

</details>

#### keeps machine instruction register constructors available

- keeps machine instruction register constructors available


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps machine instruction register constructors available")
val source = read_native_source("src/compiler/70.backend/backend/native/mach_inst.spl")

expect(source).to_contain("struct MachReg")
expect(source).to_contain("fn virtual_reg(id: i64) -> MachReg")
```

</details>

#### keeps register allocation and x86 encoding entrypoints available

- keeps register allocation and x86 encoding entrypoints available


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps register allocation and x86 encoding entrypoints available")
val regalloc_source = read_native_source("src/compiler/70.backend/backend/native/regalloc.spl")
val encode_source = read_native_source("src/compiler/70.backend/backend/native/encode_x86_64.spl")

expect(regalloc_source).to_contain("fn linear_scan_x86_64")
expect(encode_source).to_contain("fn encode_function(func: MachFunction)")
```

</details>

#### keeps native module target entrypoints available

- keeps native module target entrypoints available


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps native module target entrypoints available")
val source = read_native_source("src/compiler/70.backend/backend/native/mod.spl")

expect(source).to_contain("fn compile_native_x86_64(module: MirModule)")
expect(source).to_contain("fn target_to_arch_byte(target: CodegenTarget)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Native Backend.
- Native Backend

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

- Canonical SPipe generation for source `92ad221dab39aeaadbf309592e0bc1fe25fa375a7c83ac346b3a75857398c31a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `92ad221dab39aeaadbf309592e0bc1fe25fa375a7c83ac346b3a75857398c31a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `92ad221dab39aeaadbf309592e0bc1fe25fa375a7c83ac346b3a75857398c31a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/native_backend_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/native_backend_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/native_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/native_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/native_backend_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps ELF byte-buffer primitives available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/native_backend_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps machine instruction register constructors available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/native_backend_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps register allocation and x86 encoding entrypoints available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
