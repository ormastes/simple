# Per-Owner Allocation Attribution Gate (SIMPLE_MEM_ATTR)

> `SIMPLE_MEM_ATTR=1` (plan M1, `src/compiler_rust/runtime/src/value/heap.rs`) gates per-owner allocation attribution: `rt_mem_attr_set_owner(name)` tags subsequent allocations on the calling thread to `name`, and `rt_mem_attr_report(n)` surfaces the top-`n` owners by live bytes as `"name\tlive\tpeak\tallocs"` rows. Unset is the zero-overhead-when-off default - `mem_attr_enabled()` is a single cached `OnceLock<bool>` read, and `set_current_owner`/`note_attr_alloc`/`note_attr_free` all no-op on that one check (no registry write, no lock, no thread-local write).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Per-Owner Allocation Attribution Gate (SIMPLE_MEM_ATTR)

`SIMPLE_MEM_ATTR=1` (plan M1, `src/compiler_rust/runtime/src/value/heap.rs`) gates per-owner allocation attribution: `rt_mem_attr_set_owner(name)` tags subsequent allocations on the calling thread to `name`, and `rt_mem_attr_report(n)` surfaces the top-`n` owners by live bytes as `"name\tlive\tpeak\tallocs"` rows. Unset is the zero-overhead-when-off default - `mem_attr_enabled()` is a single cached `OnceLock<bool>` read, and `set_current_owner`/`note_attr_alloc`/`note_attr_free` all no-op on that one check (no registry write, no lock, no thread-local write).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/runtime/mem_attr_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`SIMPLE_MEM_ATTR=1` (plan M1, `src/compiler_rust/runtime/src/value/heap.rs`)
gates per-owner allocation attribution: `rt_mem_attr_set_owner(name)` tags
subsequent allocations on the calling thread to `name`, and
`rt_mem_attr_report(n)` surfaces the top-`n` owners by live bytes as
`"name\tlive\tpeak\tallocs"` rows. Unset is the zero-overhead-when-off
default - `mem_attr_enabled()` is a single cached `OnceLock<bool>` read, and
`set_current_owner`/`note_attr_alloc`/`note_attr_free` all no-op on that one
check (no registry write, no lock, no thread-local write).

`test/03_system/check/mem_attr_report_spec.spl` already proves the
string-workload round trip end-to-end. This spec instead locks in the gate
itself as an ON/OFF *behavior* switch, not just a stats-function stub: tagging
an owner while the gate is off must leave no trace in the report (because
`set_current_owner` returns before touching the registry at all), while
tagging the same owner with the gate on must register it as a report row.
That contrast is the direct evidence the gate changes real behavior, not just
a cosmetic flag.

## Key Concepts

| Concept | Description |
|---------|-------------|
| SIMPLE_MEM_ATTR | Env var gate; unset = disabled, `1` = attribution enabled |
| rt_mem_attr_set_owner | No-ops (does not touch the registry) when the gate is off |
| rt_mem_attr_report | Empty text when the gate is off; top-n owner rows when on |

## Related Specifications

- test/01_unit/runtime/mem_extern_parity_spec.spl — sibling callable/sanity spec (no gate proof)
- test/03_system/check/mem_attr_report_spec.spl — sibling out-of-process byte-attribution spec
- doc/02_requirements/runtime/memory_analysis/feature_per_owner_allocation_attribution.md

## Scenarios

### SIMPLE_MEM_ATTR per-owner allocation attribution gate

#### is disabled by default: rt_mem_attr_enabled() is 0 in this process

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is disabled by default: rt_mem_attr_enabled() is 0 in this process
- Query rt_mem_attr_enabled() without SIMPLE_MEM_ATTR set


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("is disabled by default: rt_mem_attr_enabled() is 0 in this process")
step("Query rt_mem_attr_enabled() without SIMPLE_MEM_ATTR set")
assert_equal(rt_mem_attr_enabled(), 0)
```

</details>

#### leaves no trace when an owner is tagged while the gate is off

- leaves no trace when an owner is tagged while the gate is off
- Tag an owner with the gate unset
- Confirm the report contains no row for that owner - set_current_owner no-oped


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("leaves no trace when an owner is tagged while the gate is off")
step("Tag an owner with the gate unset")
rt_mem_attr_set_owner(OWNER_NAME)

step("Confirm the report contains no row for that owner - set_current_owner no-oped")
val report = rt_mem_attr_report(10)
assert_equal(report.contains(OWNER_NAME), false)
```

</details>

#### registers the tagged owner as a report row in a child process with SIMPLE_MEM_ATTR=1

- registers the tagged owner as a report row in a child process with SIMPLE_MEM_ATTR=1
- Run the attribution gate probe fixture with SIMPLE_MEM_ATTR=1
- Confirm the child process exited cleanly
- Confirm the child observed the gate enabled
- Confirm the tagged owner appears as a row between the report markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("registers the tagged owner as a report row in a child process with SIMPLE_MEM_ATTR=1")
step("Run the attribution gate probe fixture with SIMPLE_MEM_ATTR=1")
val (out, err, code) = run_attr_gate_probe_child()

step("Confirm the child process exited cleanly")
assert_equal(code, 0)
assert_equal(err.contains("unknown extern function"), false)

step("Confirm the child observed the gate enabled")
expect(out).to_contain("attr_gate_probe: enabled=1")

step("Confirm the tagged owner appears as a row between the report markers")
val begin_idx = out.find("attr_gate_probe_report_begin")
val end_idx = out.find("attr_gate_probe_report_end")
assert_equal(begin_idx >= 0, true)
assert_equal(end_idx > begin_idx, true)
val report_body = out.substring(begin_idx, end_idx)
assert_equal(report_body.contains(OWNER_NAME), true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-MEM-ATTR-GATE-001`
- `REQ-SSPEC-RUNTIME`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `89769f2482f486e6e08dd7d4545bbeb90c8a522150e3036dd06dec56eb323bc3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `89769f2482f486e6e08dd7d4545bbeb90c8a522150e3036dd06dec56eb323bc3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `89769f2482f486e6e08dd7d4545bbeb90c8a522150e3036dd06dec56eb323bc3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/runtime/mem_attr_gate_spec.spl
mirror: doc/06_spec/01_unit/runtime/mem_attr_gate_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/runtime/mem_attr_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/runtime/mem_attr_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/runtime/mem_attr_gate_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/runtime/mem_attr_gate_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is disabled by default: rt_mem_attr_enabled() is 0 in this process' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/mem_attr_gate_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves no trace when an owner is tagged while the gate is off' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/mem_attr_gate_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers the tagged owner as a report row in a child process with SIMPLE_MEM_ATTR=1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
