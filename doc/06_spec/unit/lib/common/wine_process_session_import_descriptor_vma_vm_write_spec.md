# Wine Process Session Import Descriptor Vma Vm Write Specification

> Tests covering Wine process import descriptor VMA VM writes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Import Descriptor Vma Vm Write Specification

## Scenarios

### Wine process import descriptor VMA VM writes

#### blocks descriptor thunk VMA patching without patched image when PEB/TEB VM byte writes fail

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- blocks descriptor thunk VMA patching without patched image when PEB/TEB VM byte writes fail
   - Expected: result.ok is false
   - Expected: result.error equals `peb-teb-vm-write:bytes:layout:write:peb-write:page-fault-unmapped`
   - Expected: result.patched_image.len() equals `0`
   - Expected: result.mapped_base equals `0`
   - Expected: result.mapped_size equals `0`
   - Expected: result.patched_count equals `0`
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks descriptor thunk VMA patching without patched image when PEB/TEB VM byte writes fail")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, wine_vm_process_space_new(10, 30, "pid fs ipc net capability"))
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_process_apply_import_descriptor_thunk_patches_in_vma_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 4, 8, vm_writes)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("peb-teb-vm-write:bytes:layout:write:peb-write:page-fault-unmapped")
expect(result.patched_image.len()).to_equal(0)
expect(result.mapped_base).to_equal(0)
expect(result.mapped_size).to_equal(0)
expect(result.patched_count).to_equal(0)
expect(result.evidence).to_contain("import-descriptor-vma-thunk-patches-blocked")
expect(result.evidence).to_contain("no-vma-thunk-written")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("rejected")
```

</details>

#### blocks descriptor thunk VMA patching without patched image when descriptor planning rejects

- blocks descriptor thunk VMA patching without patched image when descriptor planning rejects
   - Expected: result.ok is false
   - Expected: result.error equals `invalid-import-descriptor-limit`
   - Expected: result.patched_image.len() equals `0`
   - Expected: result.mapped_base equals `0`
   - Expected: result.mapped_size equals `0`
   - Expected: result.patched_count equals `0`
   - Expected: result.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks descriptor thunk VMA patching without patched image when descriptor planning rejects")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_import_descriptor_thunk_patches_in_vma_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 0, 8, _ready_vm_writes())

expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-import-descriptor-limit")
expect(result.patched_image.len()).to_equal(0)
expect(result.mapped_base).to_equal(0)
expect(result.mapped_size).to_equal(0)
expect(result.patched_count).to_equal(0)
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("import-descriptor-vma-thunk-patches-blocked")
expect(result.evidence).to_contain("no-vma-thunk-written")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_process_session_import_descriptor_vma_vm_write_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine process import descriptor VMA VM writes.
- Wine process import descriptor VMA VM writes

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

- Canonical SPipe generation for source `c79be84787f28cd4fead80e5f47e92ca2c49a0cfa9a73e749b8a5e94029e7d39`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c79be84787f28cd4fead80e5f47e92ca2c49a0cfa9a73e749b8a5e94029e7d39`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c79be84787f28cd4fead80e5f47e92ca2c49a0cfa9a73e749b8a5e94029e7d39`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/wine_process_session_import_descriptor_vma_vm_write_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_process_session_import_descriptor_vma_vm_write_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_process_session_import_descriptor_vma_vm_write_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_process_session_import_descriptor_vma_vm_write_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_process_session_import_descriptor_vma_vm_write_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_process_session_import_descriptor_vma_vm_write_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks descriptor thunk VMA patching without patched image when PEB/TEB VM byte writes fail' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_process_session_import_descriptor_vma_vm_write_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks descriptor thunk VMA patching without patched image when descriptor planning rejects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
