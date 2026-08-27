# Startup Receipt Specification

> Tests covering startup receipt records what startup actually did, startup receipt off-hot-path property (§6.6 evidence levels).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Startup Receipt Specification

## Scenarios

### startup receipt records what startup actually did

#### compact receipt fields match the plan and decision they came from

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compact receipt fields match the plan and decision they came from


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compact receipt fields match the plan and decision they came from")
val m = script_startup_metadata()
val args = ["--alpha", "--beta"]
val plan = startup_plan_from_metadata("app/main.spl", args, m, true, false)
val d = startup_load_decision(m, true, false)
val r = startup_receipt_record(startup_evidence_compact(), plan, d)
assert_true(r.recorded)
assert_eq(r.schema, 1)
assert_eq(r.evidence_level, "compact")
assert_eq(r.entry_kind, plan.entry_kind)
assert_eq(r.entry_path, "app/main.spl")
assert_eq(r.load_policy, d.load_policy)
assert_eq(r.cache_strategy, d.cache_strategy)
assert_eq(r.preload_mode, d.preload_mode)
assert_eq(r.include_mmap_cache, d.include_mmap_cache)
# program_args are normalized with entry_path prepended as argv0
assert_eq(r.program_args_count, plan.program_args.len())
assert_eq(r.program_args_count, 3)
assert_eq(r.native_dynlib_count, plan.load_native_dynlibs.len())
assert_eq(r.smf_dynlib_count, plan.load_smf_dynlibs.len())
assert_eq(r.decision_supported, d.supported)
```

</details>

#### SDN rendering carries the recorded facts

- SDN rendering carries the recorded facts


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SDN rendering carries the recorded facts")
val m = script_startup_metadata()
val plan = startup_plan_from_metadata("app/main.spl", ["x"], m, true, false)
val d = startup_load_decision(m, true, false)
val r = startup_receipt_record(startup_evidence_compact(), plan, d)
val sdn = render_startup_receipt_sdn(r)
assert_true(sdn.contains("startup_receipt:"))
assert_true(sdn.contains("entry_path: app/main.spl"))
assert_true(sdn.contains("load_policy: " + d.load_policy))
assert_true(sdn.contains("program_args_count: " + plan.program_args.len().to_text()))
```

</details>

#### full level records the same facts and marks the level

- full level records the same facts and marks the level


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full level records the same facts and marks the level")
val m = script_startup_metadata()
val plan = startup_plan_from_metadata("app/main.spl", [], m, true, false)
val d = startup_load_decision(m, true, false)
val r = startup_receipt_record(startup_evidence_full(), plan, d)
assert_true(r.recorded)
assert_eq(r.evidence_level, "full")
assert_eq(r.entry_kind, plan.entry_kind)
```

</details>

### startup receipt off-hot-path property (§6.6 evidence levels)

#### level none records nothing and renders zero bytes

- level none records nothing and renders zero bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("level none records nothing and renders zero bytes")
val m = script_startup_metadata()
val plan = startup_plan_from_metadata("app/main.spl", ["a"], m, true, false)
val d = startup_load_decision(m, true, false)
val r = startup_receipt_record(startup_evidence_none(), plan, d)
assert_false(r.recorded)
assert_eq(r.entry_path, "")
assert_eq(r.program_args_count, 0)
assert_eq(render_startup_receipt_sdn(r), "")
```

</details>

#### unknown evidence level fails closed to an unrecorded receipt

- unknown evidence level fails closed to an unrecorded receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown evidence level fails closed to an unrecorded receipt")
val m = script_startup_metadata()
val plan = startup_plan_from_metadata("app/main.spl", [], m, true, false)
val d = startup_load_decision(m, true, false)
val r = startup_receipt_record("verbose", plan, d)
assert_false(r.recorded)
assert_eq(r.evidence_level, "none")
assert_eq(render_startup_receipt_sdn(r), "")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/startup/startup_receipt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering startup receipt records what startup actually did, startup receipt off-hot-path property (§6.6 evidence levels).
- startup receipt records what startup actually did
- startup receipt off-hot-path property (§6.6 evidence levels)

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

- Canonical SPipe generation for source `7a3ce73b18459b1f33e125c414cbd041dd6059dfb352c87d65a29d134408e234`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7a3ce73b18459b1f33e125c414cbd041dd6059dfb352c87d65a29d134408e234`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7a3ce73b18459b1f33e125c414cbd041dd6059dfb352c87d65a29d134408e234`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/startup/startup_receipt_spec.spl
mirror: doc/06_spec/01_unit/app/startup/startup_receipt_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/startup/startup_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/startup/startup_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/startup/startup_receipt_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compact receipt fields match the plan and decision they came from' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/startup_receipt_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SDN rendering carries the recorded facts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/startup_receipt_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'full level records the same facts and marks the level' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
