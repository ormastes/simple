# Wine Process Session Import Vma Patch Specification

> Tests covering Wine process session import descriptor VMA patching.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Import Vma Patch Specification

## Scenarios

### Wine process session import descriptor VMA patching

#### applies descriptor-qualified modeled procedure addresses through a VMA write window

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- applies descriptor-qualified modeled procedure addresses through a VMA write window
   - Expected: result.ok is true
   - Expected: result.patched_count equals `4`
   - Expected: result.mapped_base equals `0x400000`
   - Expected: result.patched_image[0x260] as i64 equals `0x80`
   - Expected: result.patched_image[0x270] as i64 equals `0x05`
   - Expected: result.patched_image[0x272] as i64 equals `0x12`
   - Expected: result.patched_image[0x390] as i64 equals `0xf0`
   - Expected: result.patched_image[0x3a0] as i64 equals `0x06`
   - Expected: result.patched_image[0x3a1] as i64 equals `0x10`
   - Expected: result.patched_image[0x3a2] as i64 equals `0x12`
   - Expected: result.status equals `import-descriptor-vma-thunk-patches-applied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies descriptor-qualified modeled procedure addresses through a VMA write window")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_import_descriptor_thunk_patches_in_vma(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.patched_count).to_equal(4)
expect(result.mapped_base).to_equal(0x400000)
expect(result.patched_image[0x260] as i64).to_equal(0x80)
expect(result.patched_image[0x270] as i64).to_equal(0x05)
expect(result.patched_image[0x272] as i64).to_equal(0x12)
expect(result.patched_image[0x390] as i64).to_equal(0xf0)
expect(result.patched_image[0x3a0] as i64).to_equal(0x06)
expect(result.patched_image[0x3a1] as i64).to_equal(0x10)
expect(result.patched_image[0x3a2] as i64).to_equal(0x12)
expect(result.evidence).to_contain("import-descriptor-iat-rvas-recorded")
expect(result.evidence).to_contain("process-vma-write-enabled")
expect(result.evidence).to_contain("process-vma-rx-restored")
expect(result.evidence).to_contain("multi-dll-import-thunks-applied")
expect(result.status).to_equal("import-descriptor-vma-thunk-patches-applied")
```

</details>

#### keeps VMA patching behind modeled import resolution

- keeps VMA patching behind modeled import resolution
   - Expected: result.ok is false
   - Expected: result.error equals `import-proc-address:USER32.dll!DialogBoxW:proc-not-found`
   - Expected: result.patched_count equals `0`
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps VMA patching behind modeled import resolution")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_import_descriptor_thunk_patches_in_vma(plan, _known_hello_with_missing_user32_proc(), 4, 8)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("import-proc-address:USER32.dll!DialogBoxW:proc-not-found")
expect(result.patched_count).to_equal(0)
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_import_vma_patch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine process session import descriptor VMA patching.
- Wine process session import descriptor VMA patching

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d74164bd22717b2eebac4a4bf31438d9bba6417f5188f12ab2f96b062dbac0a1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d74164bd22717b2eebac4a4bf31438d9bba6417f5188f12ab2f96b062dbac0a1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d74164bd22717b2eebac4a4bf31438d9bba6417f5188f12ab2f96b062dbac0a1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/wine_process_session_import_vma_patch_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_process_session_import_vma_patch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_process_session_import_vma_patch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_process_session_import_vma_patch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_process_session_import_vma_patch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_process_session_import_vma_patch_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies descriptor-qualified modeled procedure addresses through a VMA write window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_process_session_import_vma_patch_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps VMA patching behind modeled import resolution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
