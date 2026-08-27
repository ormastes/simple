# Simpleos Wine Process Vma Thunk Write Specification

> Tests covering SimpleOS Wine VMA thunk writes, REQ-027: bounded process VMA thunk patch window.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Vma Thunk Write Specification

## Scenarios

### SimpleOS Wine VMA thunk writes

### REQ-027: bounded process VMA thunk patch window

#### patch known thunk slots through a bounded process VMA write window

- patch known thunk slots through a bounded process VMA write window
   - Expected: result.ok is true
   - Expected: result.patched_count equals `3`
   - Expected: _read_u64_le(result.patched_image, get_std_handle_offset) equals `0x120000 + 5`
   - Expected: _read_u64_le(result.patched_image, write_file_offset) equals `0x120000 + 6`
   - Expected: _read_u64_le(result.patched_image, exit_process_offset) equals `0x120000 + 7`
   - Expected: result.status equals `vma-thunk-patches-applied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-027
# @req REQ-SSPEC-SYSTEM
step("patch known thunk slots through a bounded process VMA write window")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_known_kernel32_thunk_patches_in_vma(plan, wine_known_hello_exe_fixture_bytes(), 8)
val get_std_handle_offset = pe_rva_to_file_offset(result.patched_image, 0x2060)
val write_file_offset = pe_rva_to_file_offset(result.patched_image, 0x2068)
val exit_process_offset = pe_rva_to_file_offset(result.patched_image, 0x2070)
expect(result.ok).to_equal(true)
expect(result.patched_count).to_equal(3)  # oracle: result.patched_count must equal 3 — authoritative contract constant
expect(_read_u64_le(result.patched_image, get_std_handle_offset)).to_equal(0x120000 + 5)
expect(_read_u64_le(result.patched_image, write_file_offset)).to_equal(0x120000 + 6)
expect(_read_u64_le(result.patched_image, exit_process_offset)).to_equal(0x120000 + 7)
expect(result.evidence).to_contain("process-image-mapped")
expect(result.evidence).to_contain("process-vma-write-window")
expect(result.evidence).to_contain("process-vma-write-enabled")
expect(result.evidence).to_contain("process-vma-rx-restored")
expect(result.evidence).to_contain("no-host-code-jump")
expect(result.status).to_equal("vma-thunk-patches-applied")
```

</details>

#### reject VMA thunk writes before record planning passes

- reject VMA thunk writes before record planning passes
   - Expected: result.ok is false
   - Expected: result.error equals `invalid-symbol-limit`
   - Expected: result.patched_image.len() equals `0`
   - Expected: result.mapped_base equals `0`
   - Expected: result.mapped_size equals `0`
   - Expected: result.patched_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reject VMA thunk writes before record planning passes")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_known_kernel32_thunk_patches_in_vma(plan, wine_known_hello_exe_fixture_bytes(), 0)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-symbol-limit")
expect(result.patched_image.len()).to_equal(0)  # oracle: result.patched_image.len() must equal 0 — authoritative contract constant
expect(result.mapped_base).to_equal(0)  # oracle: result.mapped_base must equal 0 — authoritative contract constant
expect(result.mapped_size).to_equal(0)  # oracle: result.mapped_size must equal 0 — authoritative contract constant
expect(result.patched_count).to_equal(0)  # oracle: result.patched_count must equal 0 — authoritative contract constant
expect(result.evidence).to_contain("vma-thunk-patches-blocked")
expect(result.evidence).to_contain("no-vma-thunk-written")
expect(result.evidence).to_contain("no-arbitrary-execution")
```

</details>

#### require PEB/TEB VM byte-write readback before VMA thunk writes

- require PEB/TEB VM byte-write readback before VMA thunk writes
   - Expected: result.ok is true
   - Expected: result.patched_count equals `3`
   - Expected: result.status equals `vma-thunk-patches-applied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("require PEB/TEB VM byte-write readback before VMA thunk writes")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_process_apply_known_kernel32_thunk_patches_in_vma_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, vm_writes)

expect(result.ok).to_equal(true)
expect(result.patched_count).to_equal(3)  # oracle: result.patched_count must equal 3 — authoritative contract constant
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("tls-callback-dispatch-empty")
expect(result.evidence).to_contain("process-vma-write-window")
expect(result.evidence).to_contain("no-host-code-jump")
expect(result.status).to_equal("vma-thunk-patches-applied")
```

</details>

#### reject VM-gated VMA thunk writes before record planning passes without patched image

- reject VM-gated VMA thunk writes before record planning passes without patched image
   - Expected: result.ok is false
   - Expected: result.error equals `invalid-symbol-limit`
   - Expected: result.patched_image.len() equals `0`
   - Expected: result.mapped_base equals `0`
   - Expected: result.mapped_size equals `0`
   - Expected: result.patched_count equals `0`
   - Expected: result.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reject VM-gated VMA thunk writes before record planning passes without patched image")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_known_kernel32_thunk_patches_in_vma_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 0, _ready_vm_writes())

expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-symbol-limit")
expect(result.patched_image.len()).to_equal(0)  # oracle: result.patched_image.len() must equal 0 — authoritative contract constant
expect(result.mapped_base).to_equal(0)  # oracle: result.mapped_base must equal 0 — authoritative contract constant
expect(result.mapped_size).to_equal(0)  # oracle: result.mapped_size must equal 0 — authoritative contract constant
expect(result.patched_count).to_equal(0)  # oracle: result.patched_count must equal 0 — authoritative contract constant
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("vma-thunk-patches-blocked")
expect(result.evidence).to_contain("no-vma-thunk-written")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_vma_thunk_write_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine VMA thunk writes, REQ-027: bounded process VMA thunk patch window.
- SimpleOS Wine VMA thunk writes
- REQ-027: bounded process VMA thunk patch window

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

- `REQ-SSPEC-SYSTEM`
- `REQ-027`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `169d93663b77e30c5108472c59a900effaa0a2568021f90819d67600653339f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `169d93663b77e30c5108472c59a900effaa0a2568021f90819d67600653339f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `169d93663b77e30c5108472c59a900effaa0a2568021f90819d67600653339f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/app/simpleos/feature/simpleos_wine_process_vma_thunk_write_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_vma_thunk_write_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_vma_thunk_write_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_vma_thunk_write_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
