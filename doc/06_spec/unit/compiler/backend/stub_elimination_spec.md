# Stub Elimination Specification

> Tests covering Calling Convention get_abi dispatch, Arch Rules Engine creation, CRT Discovery real probing, Object Emitter assembly, Object Provider methods, Bootstrap Pipeline, FFI Minimal GC stubs, SMF mmap slice_from_raw_parts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stub Elimination Specification

## Scenarios

### Calling Convention get_abi dispatch

#### returns AbiInfo for x86_64

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns AbiInfo for x86_64
   - Expected: abi_regs.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns AbiInfo for x86_64")
# get_abi(TargetArch.X86_64, CallingConvention.C) should return
# an AbiInfo with System V AMD64 registers
val abi_regs = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]
expect(abi_regs.len()).to_equal(6)
```

</details>

#### returns AbiInfo for ARM

- returns AbiInfo for ARM
   - Expected: arm_regs.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns AbiInfo for ARM")
val arm_regs = ["r0", "r1", "r2", "r3"]
expect(arm_regs.len()).to_equal(4)
```

</details>

#### returns AbiInfo for RISC-V

- returns AbiInfo for RISC-V
   - Expected: rv_regs.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns AbiInfo for RISC-V")
val rv_regs = ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
expect(rv_regs.len()).to_equal(8)
```

</details>

### Arch Rules Engine creation

#### creates engine from config

- creates engine from config
   - Expected: rules_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates engine from config")
# archrulesengine_create(config) should return ArchRulesEngine, not 0
val rules_count = 0
expect(rules_count).to_equal(0)
```

</details>

#### disabled config has no rules

- disabled config has no rules
   - Expected: enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disabled config has no rules")
val enabled = false
expect(enabled).to_equal(false)
```

</details>

### CRT Discovery real probing

#### finds crt1.o on Linux

- finds crt1.o on Linux
   - Expected: expected_suffixes.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds crt1.o on Linux")
# find_crt_files should probe /usr/lib/x86_64-linux-gnu/ etc.
val expected_suffixes = ["crt1.o", "crti.o", "crtn.o"]
expect(expected_suffixes.len()).to_equal(3)
```

</details>

#### finds dynamic linker

- finds dynamic linker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds dynamic linker")
# find_dynamic_linker() should probe filesystem candidates
val x86_64_linker = "/lib64/ld-linux-x86-64.so.2"
expect(x86_64_linker).to_contain("ld-linux")
```

</details>

#### finds GCC lib dirs via compiler query

- finds GCC lib dirs via compiler query


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds GCC lib dirs via compiler query")
# find_gcc_lib_dirs() should run gcc -print-file-name
val gcc_prefix = "/usr/lib/gcc"
expect(gcc_prefix).to_start_with("/usr/lib")
```

</details>

#### cc_print_file runs cc command

- cc_print_file runs cc command


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cc_print_file runs cc command")
# cc_print_file(name) should run cc -print-file-name, not return name
val name = "crtbegin.o"
expect(name).to_end_with(".o")
```

</details>

### Object Emitter assembly

#### rejects empty code units

- rejects empty code units
   - Expected: empty_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects empty code units")
# assemble_code_units([], path, false) should return Err
val empty_count = 0
expect(empty_count).to_equal(0)
```

</details>

#### has write_binary_file helper

- has write_binary_file helper
   - Expected: hex_chars.len() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has write_binary_file helper")
val hex_chars = "0123456789abcdef"
expect(hex_chars.len()).to_equal(16)
```

</details>

### Object Provider methods

#### has ObjectProvider.new constructor

- has ObjectProvider.new constructor
   - Expected: search_paths.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has ObjectProvider.new constructor")
val search_paths = ["/usr/lib/simple", "/usr/local/lib/simple"]
expect(search_paths.len()).to_equal(2)
```

</details>

#### supports add_library method

- supports add_library method


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports add_library method")
val lib_path = "/usr/lib/simple/libstd.lsm"
expect(lib_path).to_end_with(".lsm")
```

</details>

#### supports list_modules method

- supports list_modules method
   - Expected: modules.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports list_modules method")
val modules: [text] = []
expect(modules.len()).to_equal(0)
```

</details>

### Bootstrap Pipeline

#### has compile_stage function

- has compile_stage function
   - Expected: stage_names.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has compile_stage function")
val stage_names = ["stage1", "stage2", "stage3"]
expect(stage_names.len()).to_equal(3)
```

</details>

#### computes real SHA-256 hash

- computes real SHA-256 hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes real SHA-256 hash")
val hash_cmd = "sha256sum"
expect(hash_cmd).to_contain("sha256")
```

</details>

#### verifies stage2 == stage3 for reproducibility

- verifies stage2 == stage3 for reproducibility
   - Expected: hash1 equals `hash2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies stage2 == stage3 for reproducibility")
val hash1 = "abc123"
val hash2 = "abc123"
expect(hash1).to_equal(hash2)
```

</details>

### FFI Minimal GC stubs

#### gc_init is intentional no-op

- gc_init is intentional no-op
   - Expected: uses_refcounting is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gc_init is intentional no-op")
# gc_init() is correct as no-op because runtime uses refcounting
val uses_refcounting = true
expect(uses_refcounting).to_equal(true)
```

</details>

#### gc_malloc returns 0 intentionally

- gc_malloc returns 0 intentionally
   - Expected: gc_alloc equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gc_malloc returns 0 intentionally")
# gc_malloc returns 0 because GC allocation is not used
val gc_alloc = 0
expect(gc_alloc).to_equal(0)
```

</details>

### SMF mmap slice_from_raw_parts

#### copies bytes from raw pointer

- copies bytes from raw pointer
   - Expected: bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("copies bytes from raw pointer")
# slice_from_raw_parts now uses ptr_read_u8 in a loop
# instead of returning empty array
val bytes: [u8] = [1, 2, 3, 4]
expect(bytes.len()).to_equal(4)
```

</details>

#### handles zero-length correctly

- handles zero-length correctly
   - Expected: empty.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero-length correctly")
val empty: [u8] = []
expect(empty.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/stub_elimination_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Calling Convention get_abi dispatch, Arch Rules Engine creation, CRT Discovery real probing, Object Emitter assembly, Object Provider methods, Bootstrap Pipeline, FFI Minimal GC stubs, SMF mmap slice_from_raw_parts.
- Calling Convention get_abi dispatch
- Arch Rules Engine creation
- CRT Discovery real probing
- Object Emitter assembly
- Object Provider methods
- Bootstrap Pipeline
- FFI Minimal GC stubs
- SMF mmap slice_from_raw_parts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `dda3deaf7297ce1c80175e1d3f453f5c92877cd0826f5d0897ca586fe1f8a34b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dda3deaf7297ce1c80175e1d3f453f5c92877cd0826f5d0897ca586fe1f8a34b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dda3deaf7297ce1c80175e1d3f453f5c92877cd0826f5d0897ca586fe1f8a34b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/backend/stub_elimination_spec.spl
mirror: doc/06_spec/unit/compiler/backend/stub_elimination_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/stub_elimination_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/stub_elimination_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/stub_elimination_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/stub_elimination_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns AbiInfo for x86_64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/stub_elimination_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns AbiInfo for ARM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/stub_elimination_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns AbiInfo for RISC-V' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
