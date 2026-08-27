# host_cpu_variant_spec

> AC-10: Host CPU runtime variant selection — 20 unit tests.

<details>
<summary>Full Scenario Manual</summary>

# host_cpu_variant_spec

AC-10: Host CPU runtime variant selection — 20 unit tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/host_cpu_variant_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

AC-10: Host CPU runtime variant selection — 20 unit tests.

Covers SIMD tier ranking, hardware clamping, dispatch name qualification,
loader probing, manifest entries, and variant selection with fallback.
All helpers are self-contained (no external imports beyond io_runtime).


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4c1a057dc25c41128aa0be74d04dd7e058d8475a23ff8f96d61097ad938eb98d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4c1a057dc25c41128aa0be74d04dd7e058d8475a23ff8f96d61097ad938eb98d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4c1a057dc25c41128aa0be74d04dd7e058d8475a23ff8f96d61097ad938eb98d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/unit/lib/host_cpu_variant_spec.spl
mirror: doc/06_spec/unit/lib/host_cpu_variant_spec.md (current)
findings: 4 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=81; blocker cap makes effective=49
doc/06_spec/unit/lib/host_cpu_variant_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/host_cpu_variant_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/host_cpu_variant_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/lib/host_cpu_variant_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
<!-- sspec-maintain:scorecard:end -->
