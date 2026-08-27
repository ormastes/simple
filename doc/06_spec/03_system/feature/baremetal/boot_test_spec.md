# Bare-Metal Boot Code Integration

> Tests the integration of bare-metal boot code with the Simple runtime including BSS zeroing, data section initialization, and runtime startup. Verifies that the full boot-to-main path works across supported architectures.

<details>
<summary>Full Scenario Manual</summary>

# Bare-Metal Boot Code Integration

Tests the integration of bare-metal boot code with the Simple runtime including BSS zeroing, data section initialization, and runtime startup. Verifies that the full boot-to-main path works across supported architectures.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/boot_test_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the integration of bare-metal boot code with the Simple runtime including
BSS zeroing, data section initialization, and runtime startup. Verifies that
the full boot-to-main path works across supported architectures.

## Scenarios

### Bare-Metal Boot Code

#### x86 Multiboot

#### ARM Cortex-M Startup

#### RISC-V Machine Mode

#### Cross-Architecture


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d618de1cbf49d5512a2dfe6f887c86bbc427f31a89cfeb6d1647cd59767c8dca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d618de1cbf49d5512a2dfe6f887c86bbc427f31a89cfeb6d1647cd59767c8dca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d618de1cbf49d5512a2dfe6f887c86bbc427f31a89cfeb6d1647cd59767c8dca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **75/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/feature/baremetal/boot_test_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/boot_test_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=60 oracle=50
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=75; blocker cap makes effective=49
doc/06_spec/03_system/feature/baremetal/boot_test_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/boot_test_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/boot_test_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/feature/baremetal/boot_test_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/feature/baremetal/boot_test_spec.spl:79:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'boots minimal x86 kernel' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/feature/baremetal/boot_test_spec.spl:91:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'parses multiboot info' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/feature/baremetal/boot_test_spec.spl:95:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'sets up stack correctly' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/feature/baremetal/boot_test_spec.spl:99:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'handles VGA text mode' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
