# @manual: primary

> Purpose: Prove that custom-native x86 AVX2 execution.

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that custom-native x86 AVX2 execution.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/feature/compiler/x86_avx2_custom_native_execution_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that custom-native x86 AVX2 execution.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-FEATURE-X86-AVX2-001
doc/01_research/feature/REQ-FEATURE-X86-AVX2-001.md
doc/03_plan/feature/REQ-FEATURE-X86-AVX2-001.md
doc/04_architecture/feature/REQ-FEATURE-X86-AVX2-001.md
doc/05_design/feature/REQ-FEATURE-X86-AVX2-001.md

## Scenarios

### custom-native x86 AVX2 execution


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fdc490739ebac072778137027afda5622b3274dd3d202fe1868840aaad8380a4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fdc490739ebac072778137027afda5622b3274dd3d202fe1868840aaad8380a4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fdc490739ebac072778137027afda5622b3274dd3d202fe1868840aaad8380a4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/feature/compiler/x86_avx2_custom_native_execution_spec.spl
mirror: doc/06_spec/03_system/feature/compiler/x86_avx2_custom_native_execution_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=80 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/feature/compiler/x86_avx2_custom_native_execution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/compiler/x86_avx2_custom_native_execution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/compiler/x86_avx2_custom_native_execution_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/feature/compiler/x86_avx2_custom_native_execution_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/03_system/feature/compiler/x86_avx2_custom_native_execution_spec.spl. -->
