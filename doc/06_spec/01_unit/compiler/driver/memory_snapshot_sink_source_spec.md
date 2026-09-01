# Contract spec: test/01_unit/compiler/driver/memory_snapshot_sink_source_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/driver/memory_snapshot_sink_source_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/memory_snapshot_sink_source_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable
contracts red-visible, so a regression in the owned code fails this spec
instead of shipping silently.

## Scope and Preconditions

Precondition: the repository working tree holds the subject code under test.
Each scenario exercises the subject and asserts its observable contract; no
behavior outside the named subject is claimed.

## Primary Workflow

Run the scenarios; each one drives the subject through its pinned contract
and asserts the expected observable outcome with an executed oracle.

## Unsupported / Limitations

Only the pinned contracts are asserted here; end-to-end and integration
behavior of the surrounding system is covered by companion specs.

## Verification and Recovery

A red scenario names the contract that regressed. Recover by restoring the
pinned behavior in the subject; verify with
`bin/simple test test/01_unit/compiler/driver/memory_snapshot_sink_source_spec.spl` and a green Results line.

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
expect(source).to_not_contain("file_append(sink, line")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c4fc320ab02b71ba1df74c07dfa0cbaa5ffc913d85426b8d844002c76dc0fde8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c4fc320ab02b71ba1df74c07dfa0cbaa5ffc913d85426b8d844002c76dc0fde8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c4fc320ab02b71ba1df74c07dfa0cbaa5ffc913d85426b8d844002c76dc0fde8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/compiler/driver/memory_snapshot_sink_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/memory_snapshot_sink_source_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/driver/memory_snapshot_sink_source_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps environment access and the descriptor in one owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/memory_snapshot_sink_source_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records all four exact HIR boundaries and closes normally' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/memory_snapshot_sink_source_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes only scalar cardinalities into runtime-owned formatting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
