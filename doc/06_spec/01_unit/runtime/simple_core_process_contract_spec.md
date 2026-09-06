# Simple Core Process Contract Specification

> Tests covering Simple-core process runtime.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Core Process Contract Specification

## Scenarios

### Simple-core process runtime

#### keeps process and dictionary rows on the shared tuple constructor

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps process and dictionary rows on the shared tuple constructor


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("keeps process and dictionary rows on the shared tuple constructor")
val arrays = file_read("src/runtime/simple_core/core_array.spl")
val process = file_read("src/runtime/simple_core/core_process.spl")
expect(arrays).to_contain("if array_is_valid(tuple) < 1:")
expect(arrays).to_contain("if len < 0:")
expect(arrays).to_contain("set_array_len(tuple, len)")
expect(arrays).to_not_contain("rt_array_set_len_known(tuple, len)")
expect(arrays).to_contain("val pair = rt_tuple_new(2)")
expect(process).to_contain("val result = rt_tuple_new(3)")
```

</details>

#### spawns with argv, waits for a positive pid, and returns the real exit code

- spawns with argv, waits for a positive pid, and returns the real exit code


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("spawns with argv, waits for a positive pid, and returns the real exit code")
val source = file_read("src/runtime/simple_core/core_process.spl")
expect(source).to_contain("pub fn rt_process_run(cmd_ptr: i64, cmd_len: i64, args: i64) -> i64:")
expect(source).to_contain("spl_store_i64(argv, (i + 1) * 8, rt_string_data(rt_array_get_text(args, i)))")
expect(source).to_contain("if pid < 1:")
expect(source).to_contain("execvp(command, argv)")
expect(source).to_contain("val waited = waitpid(pid, status, 0)")
expect(source).to_contain("rt_value_int(exit_code)")
expect(source.contains("return 3")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/runtime/simple_core_process_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Simple-core process runtime.
- Simple-core process runtime

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-RUNTIME`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8c6c9e476cc0841b1a64a46d1ac61e232e21f33ec90dc038753759480fb93794`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c6c9e476cc0841b1a64a46d1ac61e232e21f33ec90dc038753759480fb93794`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c6c9e476cc0841b1a64a46d1ac61e232e21f33ec90dc038753759480fb93794`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/runtime/simple_core_process_contract_spec.spl
mirror: doc/06_spec/01_unit/runtime/simple_core_process_contract_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/01_unit/runtime/simple_core_process_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/runtime/simple_core_process_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/runtime/simple_core_process_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/runtime/simple_core_process_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/runtime/simple_core_process_contract_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps process and dictionary rows on the shared tuple constructor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/simple_core_process_contract_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'spawns with argv, waits for a positive pid, and returns the real exit code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
