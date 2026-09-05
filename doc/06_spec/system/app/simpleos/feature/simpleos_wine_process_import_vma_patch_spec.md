# Simpleos Wine Process Import Vma Patch Specification

> Tests covering SimpleOS Wine import descriptor VMA patching, REQ-034: multi-DLL thunk patch application through process VMA.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Import Vma Patch Specification

## Scenarios

### SimpleOS Wine import descriptor VMA patching

### REQ-034: multi-DLL thunk patch application through process VMA

#### should apply descriptor-qualified modeled procedure addresses through a bounded VMA write window

- should apply descriptor-qualified modeled procedure addresses through a bounded VMA write window
   - Expected: result.ok is true
   - Expected: result.patched_count equals `4`
   - Expected: result.patched_image[0x260] as i64 equals `0x80`
   - Expected: result.patched_image[0x270] as i64 equals `0x05`
   - Expected: result.patched_image[0x390] as i64 equals `0xf0`
   - Expected: result.patched_image[0x3a0] as i64 equals `0x06`
   - Expected: result.status equals `import-descriptor-vma-thunk-patches-applied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
        # @req REQ-SSPEC-SYSTEM
        # @req REQ-034
    # @req REQ-034
# @req REQ-SSPEC-SYSTEM
step("should apply descriptor-qualified modeled procedure addresses through a bounded VMA write window")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_import_descriptor_thunk_patches_in_vma(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.patched_count).to_equal(4)
expect(result.patched_image[0x260] as i64).to_equal(0x80)
expect(result.patched_image[0x270] as i64).to_equal(0x05)
expect(result.patched_image[0x390] as i64).to_equal(0xf0)
expect(result.patched_image[0x3a0] as i64).to_equal(0x06)
expect(result.evidence).to_contain("import-descriptor-iat-rvas-recorded")
expect(result.evidence).to_contain("process-vma-write-enabled")
expect(result.evidence).to_contain("process-vma-rx-restored")
expect(result.evidence).to_contain("multi-dll-import-thunks-applied")
expect(result.evidence).to_contain("no-real-dll-loaded")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("import-descriptor-vma-thunk-patches-applied")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine import descriptor VMA patching, REQ-034: multi-DLL thunk patch application through process VMA.
- SimpleOS Wine import descriptor VMA patching
- REQ-034: multi-DLL thunk patch application through process VMA

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

- `REQ-SSPEC-SYSTEM`
- `REQ-034`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `af2a5a5e9ed2092ae49a51e94d472b4ff022dd5889ea3ae584ddf83b4fa6f2f8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `af2a5a5e9ed2092ae49a51e94d472b4ff022dd5889ea3ae584ddf83b4fa6f2f8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `af2a5a5e9ed2092ae49a51e94d472b4ff022dd5889ea3ae584ddf83b4fa6f2f8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.spl
mirror: doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=95 oracle=90
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should apply descriptor-qualified modeled procedure addresses through a bounded VMA write window' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should apply descriptor-qualified modeled procedure addresses through a bounded VMA write window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
