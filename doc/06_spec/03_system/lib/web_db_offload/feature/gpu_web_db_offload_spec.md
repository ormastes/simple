# Gpu Web Db Offload Specification

> Tests covering GPU web/db offload reliability-first system contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Web Db Offload Specification

## Scenarios

### GPU web/db offload reliability-first system contract

#### should prove CPU fallback when GPU is unavailable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should prove CPU fallback when GPU is unavailable
- Evaluate an unavailable GPU path
   - Expected: fallback.path equals `GpuWdbDecisionPath.CpuFallback`
   - Expected: fallback.reason equals `gpu-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should prove CPU fallback when GPU is unavailable")
step("Evaluate an unavailable GPU path")
val budget = gpu_wdb_default_budget()
val fallback = gpu_wdb_decide(
    system_request(GpuWdbWorkKind.DbVectorSearch, budget.min_gpu_batch_bytes, 0, false, true, true),
    budget
)
expect(fallback.path).to_equal(GpuWdbDecisionPath.CpuFallback)
expect(fallback.reason).to_equal("gpu-unavailable")
```

</details>

#### should prove GPU evidence when a coarse web path is eligible

- should prove GPU evidence when a coarse web path is eligible
- Evaluate an eligible coarse web rank batch
   - Expected: gpu_decision.path equals `GpuWdbDecisionPath.GpuEvidence`
   - Expected: gpu_decision.reason equals `gpu-evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should prove GPU evidence when a coarse web path is eligible")
step("Evaluate an eligible coarse web rank batch")
val budget = gpu_wdb_default_budget()
val gpu_decision = gpu_wdb_decide(
    system_request(GpuWdbWorkKind.WebRank, budget.min_gpu_batch_bytes, 0, true, true, true),
    budget
)
expect(gpu_decision.path).to_equal(GpuWdbDecisionPath.GpuEvidence)
expect(gpu_decision.reason).to_equal("gpu-evidence")
```

</details>

#### should route eligible work through a reusable GPU library plan

- should route eligible work through a reusable GPU library plan
- Build a reusable plan for an eligible embedding batch
   - Expected: plan.decision.reason equals `gpu-evidence`
   - Expected: plan.target equals `gpu_web_embedding_batch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should route eligible work through a reusable GPU library plan")
step("Build a reusable plan for an eligible embedding batch")
val budget = gpu_wdb_default_budget()
val snapshot = GpuWdbRuntimeSnapshot(
    queue_depth: 0,
    gpu_available: true,
    generation_current: true,
    cpu_fallback_available: true
)
val req = gpu_wdb_request(GpuWdbWorkKind.WebEmbedding, budget.min_gpu_batch_bytes, snapshot)
val plan = gpu_wdb_execution_plan(req, budget)
expect(plan.decision.reason).to_equal("gpu-evidence")
expect(plan.target).to_equal("gpu_web_embedding_batch")
```

</details>

#### should batch DB vector work through shared GPU queue accounting

- should batch DB vector work through shared GPU queue accounting
- Build a reusable DB vector batch plan
   - Expected: plan.execution.decision.reason equals `gpu-evidence`
   - Expected: plan.execution.target equals `gpu_db_vector_search_batch`
   - Expected: plan.queue_depth_after equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should batch DB vector work through shared GPU queue accounting")
step("Build a reusable DB vector batch plan")
val budget = gpu_wdb_default_budget()
val snapshot = GpuWdbRuntimeSnapshot(
    queue_depth: 1,
    gpu_available: true,
    generation_current: true,
    cpu_fallback_available: true
)
val window = gpu_wdb_batch_window(GpuWdbWorkKind.DbVectorSearch, budget.min_gpu_batch_bytes * 8, 8, snapshot)
val plan = gpu_wdb_batch_plan(window, budget)
expect(plan.execution.decision.reason).to_equal("gpu-evidence")
expect(plan.execution.target).to_equal("gpu_db_vector_search_batch")
expect(plan.queue_depth_after).to_equal(2)
```

</details>

#### should enforce RAM mode stale generation safety

- should enforce RAM mode stale generation safety
- RAM mode rejects stale generation
   - Expected: ram.reason equals `stale-generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should enforce RAM mode stale generation safety")
step("RAM mode rejects stale generation")
val budget = gpu_wdb_default_budget()
val ram = gpu_wdb_ram_mode_admits(budget.min_gpu_batch_bytes, false, budget)
expect(ram.reason).to_equal("stale-generation")
```

</details>

#### should enforce SSD mode WAL generation safety

- should enforce SSD mode WAL generation safety
- SSD mode rejects stale WAL generation
   - Expected: ssd.reason equals `stale-generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should enforce SSD mode WAL generation safety")
step("SSD mode rejects stale WAL generation")
val budget = gpu_wdb_default_budget()
val ssd = gpu_wdb_ssd_mode_admits(budget.min_gpu_batch_bytes, false, budget)
expect(ssd.reason).to_equal("stale-generation")
```

</details>

#### should enforce NoSQL CPU metadata filter ownership

- should enforce NoSQL CPU metadata filter ownership
- NoSQL mode rejects GPU-owned metadata filtering
   - Expected: nosql.reason equals `metadata-filter-must-stay-cpu-owned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should enforce NoSQL CPU metadata filter ownership")
step("NoSQL mode rejects GPU-owned metadata filtering")
val budget = gpu_wdb_default_budget()
val nosql = gpu_wdb_nosql_mode_admits(budget.min_gpu_batch_bytes, false, budget)
expect(nosql.reason).to_equal("metadata-filter-must-stay-cpu-owned")
```

</details>

#### should reject timing-only production GPU claims

- should reject timing-only production GPU claims
- Build an upload-only receipt with a positive synthetic handle
- Require device-origin readback before production promotion
   - Expected: gpu_wdb_device_receipt_reason(upload_only) equals `device-readback-missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject timing-only production GPU claims")
step("Build an upload-only receipt with a positive synthetic handle")
val upload_only = gpu_wdb_device_receipt(
    true, 73, 9001, "upload_only", 123456, 123456, 0, false)

step("Require device-origin readback before production promotion")
expect(gpu_wdb_device_receipt_valid(upload_only)).to_be(false)
expect(gpu_wdb_device_receipt_reason(upload_only)).to_equal("device-readback-missing")
```

</details>

#### should require exact checksum parity from the device

- should require exact checksum parity from the device
- Build exact and corrupt device readback receipts
- Accept only the exact device-origin result
   - Expected: gpu_wdb_device_receipt_reason(corrupt) equals `device-readback-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require exact checksum parity from the device")
step("Build exact and corrupt device readback receipts")
val exact = gpu_wdb_device_receipt(
    true, 73, 9001, "device_readback", 123456, 123456, 0, false)
val corrupt = gpu_wdb_device_receipt(
    true, 73, 9001, "device_readback", 123456, 123457, 1, false)

step("Accept only the exact device-origin result")
expect(gpu_wdb_device_receipt_valid(exact)).to_be(true)
expect(gpu_wdb_device_receipt_valid(corrupt)).to_be(false)
expect(gpu_wdb_device_receipt_reason(corrupt)).to_equal("device-readback-mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GPU web/db offload reliability-first system contract.
- GPU web/db offload reliability-first system contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `bcea2bed8f56cf33f331bc469b2ddcdea11b6940a792f4b874ce4b449a294b7c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bcea2bed8f56cf33f331bc469b2ddcdea11b6940a792f4b874ce4b449a294b7c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bcea2bed8f56cf33f331bc469b2ddcdea11b6940a792f4b874ce4b449a294b7c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl
mirror: doc/06_spec/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl:25:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should prove CPU fallback when GPU is unavailable' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should prove CPU fallback when GPU is unavailable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should prove GPU evidence when a coarse web path is eligible' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should prove GPU evidence when a coarse web path is eligible' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should route eligible work through a reusable GPU library plan' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should route eligible work through a reusable GPU library plan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl:65:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should batch DB vector work through shared GPU queue accounting' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should enforce RAM mode stale generation safety' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should enforce SSD mode WAL generation safety' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
