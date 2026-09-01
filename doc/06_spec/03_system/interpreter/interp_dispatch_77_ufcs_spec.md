# Interp Dispatch 77 Ufcs Specification

> Tests covering Interp dispatch repro (task 77) - UFCS free-function calls.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interp Dispatch 77 Ufcs Specification

## Scenarios

### Interp dispatch repro (task 77) - UFCS free-function calls

#### resolves a module-local free function via UFCS from an it-block

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves a module-local free function via UFCS from an it-block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves a module-local free function via UFCS from an it-block")
val v = 5
val r = v.ufcs_double_77()
expect r == 10
```

</details>

#### resolves UFCS on a struct receiver

- resolves UFCS on a struct receiver


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves UFCS on a struct receiver")
val p = Pt77Ufcs(x: 3, y: 4)
val s = p.sum_pt77_ufcs()
expect s == 7
```

</details>

#### resolves UFCS with extra positional args

- resolves UFCS with extra positional args


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves UFCS with extra positional args")
val p = Pt77Ufcs(x: 3, y: 4)
val s = p.scale_pt77_ufcs(2)
expect s == 14
```

</details>

#### resolves UFCS on a free function imported from another module

- resolves UFCS on a free function imported from another module


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves UFCS on a free function imported from another module")
val v: i64 = 5
val r = v.triple_it_77()
expect r == 15
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/03_system/interpreter/interp_dispatch_77_ufcs_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Interp dispatch repro (task 77) - UFCS free-function calls.
- Interp dispatch repro (task 77) - UFCS free-function calls

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d0ed40e84e1c51e6a1054dd424950c074499ec6a6aa4853fde8f35db4fc78ddc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d0ed40e84e1c51e6a1054dd424950c074499ec6a6aa4853fde8f35db4fc78ddc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d0ed40e84e1c51e6a1054dd424950c074499ec6a6aa4853fde8f35db4fc78ddc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/interpreter/interp_dispatch_77_ufcs_spec.spl
mirror: doc/06_spec/03_system/interpreter/interp_dispatch_77_ufcs_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/interpreter/interp_dispatch_77_ufcs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/interpreter/interp_dispatch_77_ufcs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/interpreter/interp_dispatch_77_ufcs_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a module-local free function via UFCS from an it-block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/interpreter/interp_dispatch_77_ufcs_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves UFCS on a struct receiver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/interpreter/interp_dispatch_77_ufcs_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves UFCS with extra positional args' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
