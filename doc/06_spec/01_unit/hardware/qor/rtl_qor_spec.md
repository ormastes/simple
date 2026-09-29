# Rtl Qor Specification

> Tests covering RTL QoR run model, RTL QoR comparison, RTL QoR store, RTL QoR reports.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rtl Qor Specification

## Scenarios

### RTL QoR run model

#### computes area score with weighted hard macros

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- computes area score with weighted hard macros


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes area score with weighted hard macros")
val run = baseline_run()
expect run.area_score() == 2300
```

</details>

#### serializes to SDN-style storage text

- serializes to SDN-style storage text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes to SDN-style storage text")
val sdn = baseline_run().to_sdn()
check(sdn.starts_with("rtl_qor_run"))
```

</details>

### RTL QoR comparison

#### computes deltas and improvement predicates

- computes deltas and improvement predicates


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes deltas and improvement predicates")
val delta = compare_qor_runs(baseline_run(), candidate_run())
expect delta.lut_delta == -80
expect delta.ff_delta == -20
expect delta.fmax_delta == 5
check(delta.improved_area())
check(delta.improved_fmax())
```

</details>

### RTL QoR store

#### stores runs and serializes them

- stores runs and serializes them


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores runs and serializes them")
val store = RtlQorStore.empty().with_run(baseline_run()).with_run(candidate_run())
expect store.len() == 2
val latest = store.latest_for_design("rv32i_core")
check(latest.?)
expect latest.unwrap().run_id == "cand"
```

</details>

### RTL QoR reports

#### renders run and comparison markdown

- renders run and comparison markdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders run and comparison markdown")
val run_md = rtl_qor_run_markdown(baseline_run())
val compare_md = rtl_qor_compare_markdown(baseline_run(), candidate_run())
check(run_md.contains("RTL QoR Run"))
check(compare_md.contains("RTL QoR Delta"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/hardware/qor/rtl_qor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RTL QoR run model, RTL QoR comparison, RTL QoR store, RTL QoR reports.
- RTL QoR run model
- RTL QoR comparison
- RTL QoR store
- RTL QoR reports

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `85aeac6e332c5a9900ced05544c4890039dc83f3f1e9db7c0520787e1d8df242`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `85aeac6e332c5a9900ced05544c4890039dc83f3f1e9db7c0520787e1d8df242`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `85aeac6e332c5a9900ced05544c4890039dc83f3f1e9db7c0520787e1d8df242`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/hardware/qor/rtl_qor_spec.spl
mirror: doc/06_spec/01_unit/hardware/qor/rtl_qor_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/hardware/qor/rtl_qor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/hardware/qor/rtl_qor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/hardware/qor/rtl_qor_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes area score with weighted hard macros' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/qor/rtl_qor_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serializes to SDN-style storage text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/qor/rtl_qor_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes deltas and improvement predicates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
