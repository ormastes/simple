# File Char Device Registration Specification

> Tests covering rt_file_is_char_device seed/JIT registration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# File Char Device Registration Specification

## Scenarios

### rt_file_is_char_device seed/JIT registration

#### keeps the canonical (ptr, len) ABI with no stale C copy in the gpu stub

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the canonical (ptr, len) ABI with no stale C copy in the gpu stub


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the canonical (ptr, len) ABI with no stale C copy in the gpu stub")
val stub = rt_file_read_text("src/runtime/runtime_native_gpu_stub.c") ?? ""
val runtime_c = rt_file_read_text("src/runtime/runtime.c") ?? ""
val mod_rs = rt_file_read_text("src/compiler_rust/compiler/src/interpreter_extern/mod.rs") ?? ""
# The gpu stub must document the removal and must NOT define the symbol.
expect(stub).to_contain("do not")
expect(stub).to_contain("re-add a C copy")
assert_false(stub.contains("int rt_file_is_char_device(const char* path)"))
# The canonical C runtime definition uses the two-argument (ptr, len) ABI.
expect(runtime_c).to_contain("int rt_file_is_char_device(const uint8_t* path_ptr, uint64_t path_len)")
expect(runtime_c).to_contain("S_ISCHR(st.st_mode)")
# The interpreter extern table registers the name.
expect(mod_rs).to_contain("\"rt_file_is_char_device\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter_extern/file_char_device_registration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering rt_file_is_char_device seed/JIT registration.
- rt_file_is_char_device seed/JIT registration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-INTERP-EXTERN-FILE-CHAR-DEVICE-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0558914456d5973768bba92c4c6d98c99d55c511258fdc9ae23ef2d5990bd0ba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0558914456d5973768bba92c4c6d98c99d55c511258fdc9ae23ef2d5990bd0ba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0558914456d5973768bba92c4c6d98c99d55c511258fdc9ae23ef2d5990bd0ba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/interpreter_extern/file_char_device_registration_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter_extern/file_char_device_registration_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=89; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/interpreter_extern/file_char_device_registration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter_extern/file_char_device_registration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter_extern/file_char_device_registration_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/interpreter_extern/file_char_device_registration_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the canonical (ptr, len) ABI with no stale C copy in the gpu stub' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
