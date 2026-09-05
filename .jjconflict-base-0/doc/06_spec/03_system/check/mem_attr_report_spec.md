# Per-Owner Allocation Attribution Report

> `rt_mem_attr_enabled() -> i64`, `rt_mem_attr_set_owner(name: text)`, and `rt_mem_attr_report(n: i64) -> text` are the pure-Simple-callable surface for plan-M1 per-owner allocation attribution in `runtime/src/value/heap.rs`. The feature is gated by `SIMPLE_MEM_ATTR=1` and OFF by default (single cached-bool check, no lock/map/TL write on the off path). This spec proves both sides of the gate: disabled-by-default in the current process, and a child process with `SIMPLE_MEM_ATTR=1` that tags an owner, allocates, and surfaces that owner's name in the top-N report text.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Per-Owner Allocation Attribution Report

`rt_mem_attr_enabled() -> i64`, `rt_mem_attr_set_owner(name: text)`, and `rt_mem_attr_report(n: i64) -> text` are the pure-Simple-callable surface for plan-M1 per-owner allocation attribution in `runtime/src/value/heap.rs`. The feature is gated by `SIMPLE_MEM_ATTR=1` and OFF by default (single cached-bool check, no lock/map/TL write on the off path). This spec proves both sides of the gate: disabled-by-default in the current process, and a child process with `SIMPLE_MEM_ATTR=1` that tags an owner, allocates, and surfaces that owner's name in the top-N report text.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #per-owner-allocation-attribution |
| Category | Infrastructure |
| Status | In Progress |
| Requirements | doc/02_requirements/runtime/memory_analysis/feature_per_owner_allocation_attribution.md |
| Source | `test/03_system/check/mem_attr_report_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`rt_mem_attr_enabled() -> i64`, `rt_mem_attr_set_owner(name: text)`, and
`rt_mem_attr_report(n: i64) -> text` are the pure-Simple-callable surface for
plan-M1 per-owner allocation attribution in `runtime/src/value/heap.rs`. The
feature is gated by `SIMPLE_MEM_ATTR=1` and OFF by default (single cached-bool
check, no lock/map/TL write on the off path). This spec proves both sides of
the gate: disabled-by-default in the current process, and a child process
with `SIMPLE_MEM_ATTR=1` that tags an owner, allocates, and surfaces that
owner's name in the top-N report text.

## Key Concepts

| Concept | Description |
|---------|-------------|
| SIMPLE_MEM_ATTR | Env var gate; `1` enables attribution, unset/other = OFF |
| rt_mem_attr_set_owner | Tags subsequent allocations on this thread to `name` |
| rt_mem_attr_report | Top-`n` owners by live bytes as `name\tlive\tpeak\tallocs` rows |

## Related Specifications

- doc/02_requirements/runtime/memory_analysis/feature_per_owner_allocation_attribution.md
- test/03_system/check/stage4_memory_gate_spec.spl — sibling out-of-process memory spec

## Scenarios

### Per-owner allocation attribution report

#### is disabled by default in this process

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is disabled by default in this process
- Query rt_mem_attr_enabled() without SIMPLE_MEM_ATTR set
- Query rt_mem_attr_report() while disabled and expect harmless output


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is disabled by default in this process")
step("Query rt_mem_attr_enabled() without SIMPLE_MEM_ATTR set")
val enabled = rt_mem_attr_enabled()
assert_equal(enabled, 0)

step("Query rt_mem_attr_report() while disabled and expect harmless output")
val report = rt_mem_attr_report(5)
expect(report.len()).to_be_less_than(200)
```

</details>

#### surfaces a tagged owner's name in a child process with SIMPLE_MEM_ATTR=1

- surfaces a tagged owner's name in a child process with SIMPLE_MEM_ATTR=1
- Run the attr_workload fixture with SIMPLE_MEM_ATTR=1
- Confirm the child process exited cleanly
- Confirm the child observed attribution enabled and reported the owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("surfaces a tagged owner's name in a child process with SIMPLE_MEM_ATTR=1")
step("Run the attr_workload fixture with SIMPLE_MEM_ATTR=1")
val (out, _err, code) = run_attr_workload_child()

step("Confirm the child process exited cleanly")
assert_equal(code, 0)

step("Confirm the child observed attribution enabled and reported the owner")
expect(out).to_contain("enabled=1")
expect(out).to_contain("attr_spec_owner")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/runtime/memory_analysis/feature_per_owner_allocation_attribution.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-MEM-ATTR-REPORT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `52f3622632c504649052895acc11ab2c2ba89dc5354f1211a773236da4874ed6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `52f3622632c504649052895acc11ab2c2ba89dc5354f1211a773236da4874ed6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `52f3622632c504649052895acc11ab2c2ba89dc5354f1211a773236da4874ed6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/check/mem_attr_report_spec.spl
mirror: doc/06_spec/03_system/check/mem_attr_report_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/03_system/check/mem_attr_report_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/mem_attr_report_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/mem_attr_report_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/check/mem_attr_report_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is disabled by default in this process' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/mem_attr_report_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'surfaces a tagged owner's name in a child process with SIMPLE_MEM_ATTR=1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
