# Memory Snapshot Sink Source Specification

> Tests covering durable Stage3 memory snapshot ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Memory Snapshot Sink Source Specification

## Scenarios

### durable Stage3 memory snapshot ownership

#### keeps environment access and the descriptor in one owner

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps environment access and the descriptor in one owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps environment access and the descriptor in one owner")
val owner = file_read("src/compiler/80.driver/driver_mem_snapshot.spl")
val lowering = file_read("src/compiler/80.driver/driver_hir_pipeline_lowering.spl")
expect(owner).to_contain("rt_env_get(\"SIMPLE_MEM_SNAPSHOT_FILE\")")
expect(owner).to_contain("var _mem_snapshot_fd: i64 = -1")
expect(lowering).not_to_contain("SIMPLE_MEM_SNAPSHOT_FILE")
```

</details>

#### records all four exact HIR boundaries and closes normally

- records all four exact HIR boundaries and closes normally


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records all four exact HIR boundaries and closes normally")
val source = file_read("src/compiler/80.driver/driver_hir_pipeline_lowering.spl")
expect(source).to_contain("\"hir-file-start\"")
expect(source).to_contain("\"hir-post-lowering\"")
expect(source).to_contain("\"hir-post-diagnostics\"")
expect(source).to_contain("\"hir-post-store\"")
expect(source).to_contain("mem_snapshot_finish()")
```

</details>

#### passes only scalar cardinalities into runtime-owned formatting

- passes only scalar cardinalities into runtime-owned formatting


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes only scalar cardinalities into runtime-owned formatting")
val owner = file_read("src/compiler/80.driver/driver_mem_snapshot.spl")
expect(owner).to_contain("Formatting is deliberately runtime-owned")
expect(owner).to_contain("rt_mem_snapshot_record(")
expect(owner).not_to_contain("heap_live_bytes={")
```

</details>

#### binds phase records to the same durable schema and run identity

- binds phase records to the same durable schema and run identity
   - Expected: source does not contain `file_append(sink, line`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds phase records to the same durable schema and run identity")
val source = file_read("src/compiler/80.driver/driver_log_helpers.spl")
expect(source).to_contain("rt_mem_snapshot_open(sink)")
expect(source).to_contain("_g_phase_profile_seq")
expect(source).to_contain("\"phase\", msg")
expect(source).to_contain("SIMPLE_EVIDENCE_RUN_ID")
expect(source.contains("file_append(sink, line")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/memory_snapshot_sink_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering durable Stage3 memory snapshot ownership.
- durable Stage3 memory snapshot ownership

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4b0bc34a94c6dd69a3210e460fedc65ff30862b74f638a15be075a04bbb4ce3e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4b0bc34a94c6dd69a3210e460fedc65ff30862b74f638a15be075a04bbb4ce3e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4b0bc34a94c6dd69a3210e460fedc65ff30862b74f638a15be075a04bbb4ce3e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/driver/memory_snapshot_sink_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/memory_snapshot_sink_source_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/driver/memory_snapshot_sink_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/memory_snapshot_sink_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/memory_snapshot_sink_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/driver/memory_snapshot_sink_source_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps environment access and the descriptor in one owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/memory_snapshot_sink_source_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records all four exact HIR boundaries and closes normally' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/memory_snapshot_sink_source_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes only scalar cardinalities into runtime-owned formatting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
