# Simpleos Wine Process Import Descriptor Table Specification

> Tests covering SimpleOS Wine import descriptor table, REQ-029: bounded multi-DLL import descriptor inspection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Import Descriptor Table Specification

## Scenarios

### SimpleOS Wine import descriptor table

### REQ-029: bounded multi-DLL import descriptor inspection

#### should inspect multiple full-Wine import descriptors before arbitrary execution
#### should inventory descriptor-qualified thunk records without loading DLLs

- should inventory descriptor-qualified thunk records without loading DLLs
   - Expected: result.ok is true
   - Expected: result.binding_count equals `4`
   - Expected: result.dll_names[0] equals `KERNEL32.dll`
   - Expected: result.symbols[0] equals `GetStdHandle`
   - Expected: result.dll_names[3] equals `USER32.dll`
   - Expected: result.symbols[3] equals `MessageBoxW`
   - Expected: result.status equals `import-descriptor-thunks-inventoried`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should inventory descriptor-qualified thunk records without loading DLLs")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_inventory_import_descriptor_thunks(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.binding_count).to_equal(4)
expect(result.dll_names[0]).to_equal("KERNEL32.dll")
expect(result.symbols[0]).to_equal("GetStdHandle")
expect(result.dll_names[3]).to_equal("USER32.dll")
expect(result.symbols[3]).to_equal("MessageBoxW")
expect(result.evidence).to_contain("import-descriptor-thunk-bindings-data-backed")
expect(result.evidence).to_contain("import-descriptor-symbol-names-recorded")
expect(result.status).to_equal("import-descriptor-thunks-inventoried")
```

</details>

#### should plan supported import dependencies without loading DLLs

- should plan supported import dependencies without loading DLLs
   - Expected: result.ok is true
   - Expected: result.module_count equals `2`
   - Expected: result.supported_count equals `2`
   - Expected: result.modules[0] equals `KERNEL32.dll`
   - Expected: result.modules[1] equals `USER32.dll`
   - Expected: result.status equals `import-dependencies-planned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should plan supported import dependencies without loading DLLs")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_dependencies(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.module_count).to_equal(2)
expect(result.supported_count).to_equal(2)
expect(result.modules[0]).to_equal("KERNEL32.dll")
expect(result.modules[1]).to_equal("USER32.dll")
expect(result.evidence).to_contain("import-dependency-plan-bounded")
expect(result.evidence).to_contain("no-dll-loaded")
expect(result.status).to_equal("import-dependencies-planned")
```

</details>

#### should reject unsupported import dependencies before loading DLLs

- should reject unsupported import dependencies before loading DLLs
   - Expected: result.ok is false
   - Expected: result.error equals `unsupported-import-module:ADVAPI32.dll`
   - Expected: result.unsupported_modules[0] equals `ADVAPI32.dll`
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject unsupported import dependencies before loading DLLs")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_dependencies(plan, _known_hello_with_unsupported_import_descriptor(), 4, 8)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("unsupported-import-module:ADVAPI32.dll")
expect(result.unsupported_modules[0]).to_equal("ADVAPI32.dll")
expect(result.evidence).to_contain("import-dependency-unsupported-blocked")
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine import descriptor table, REQ-029: bounded multi-DLL import descriptor inspection.
- SimpleOS Wine import descriptor table
- REQ-029: bounded multi-DLL import descriptor inspection

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
- `REQ-029`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a2d973140584742faad5e17aa806931c37f28f200af7c2abd0f2cf725fe832b3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a2d973140584742faad5e17aa806931c37f28f200af7c2abd0f2cf725fe832b3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a2d973140584742faad5e17aa806931c37f28f200af7c2abd0f2cf725fe832b3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.spl:72:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should inspect multiple full-Wine import descriptors before arbitrary execution' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.spl:72:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should inspect multiple full-Wine import descriptors before arbitrary execution' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.spl:89:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should inventory descriptor-qualified thunk records without loading DLLs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should inventory descriptor-qualified thunk records without loading DLLs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.spl:104:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should plan supported import dependencies without loading DLLs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should plan supported import dependencies without loading DLLs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.spl:118:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject unsupported import dependencies before loading DLLs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject unsupported import dependencies before loading DLLs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
