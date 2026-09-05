# Rdma Specification

> Tests covering RDMA provider hardware evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rdma Specification

## Scenarios

### RDMA provider hardware evidence

#### rejects model and host SFFI modes as hardware RDMA

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects model and host SFFI modes as hardware RDMA
   - Expected: rdma_provider_readiness_reason(model) equals `rdma-not-hardware:model`
   - Expected: rdma_provider_readiness_reason(host) equals `rdma-not-hardware:sffi-host`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects model and host SFFI modes as hardware RDMA")
val model = rdma_provider_evidence(
    "model",
    "simple-driver",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "resource-grant-set:tok=41",
    "non-secure-resource-namespace"
)
val host = rdma_provider_evidence(
    "sffi-host",
    "simple-driver",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "resource-grant-set:tok=42",
    "non-secure-resource-namespace"
)

expect(rdma_provider_readiness_reason(model)).to_equal("rdma-not-hardware:model")
expect(rdma_provider_readiness_reason(host)).to_equal("rdma-not-hardware:sffi-host")
```

</details>

#### requires an issued grant token and non-secure namespace for device mode

- requires an issued grant token and non-secure namespace for device mode
   - Expected: rdma_provider_hardware_ready(no_token) is false
   - Expected: rdma_provider_readiness_reason(no_token) equals `missing-rdma-issued-grant-token:resource-grant-set`
   - Expected: rdma_provider_readiness_reason(bad_namespace) equals `missing-rdma-non-secure-namespace:secure-kernel-namespace`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires an issued grant token and non-secure namespace for device mode")
val no_token = rdma_provider_evidence(
    "device",
    "simple-driver",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "resource-grant-set",
    "non-secure-resource-namespace"
)
val bad_namespace = rdma_provider_evidence(
    "device",
    "simple-driver",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "resource-grant-set:tok=43",
    "secure-kernel-namespace"
)

expect(rdma_provider_hardware_ready(no_token)).to_equal(false)
expect(rdma_provider_readiness_reason(no_token)).to_equal("missing-rdma-issued-grant-token:resource-grant-set")
expect(rdma_provider_readiness_reason(bad_namespace)).to_equal("missing-rdma-non-secure-namespace:secure-kernel-namespace")
```

</details>

#### accepts device mode only with full PCI DMA grant and namespace evidence

- accepts device mode only with full PCI DMA grant and namespace evidence
   - Expected: rdma_provider_readiness_reason(ready) equals `ready`
   - Expected: rdma_provider_hardware_ready(ready) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts device mode only with full PCI DMA grant and namespace evidence")
val ready = rdma_provider_evidence(
    "device",
    "simple-driver",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "resource-grant-set:tok=44",
    "non-secure-resource-namespace"
)

expect(rdma_provider_readiness_reason(ready)).to_equal("ready")
expect(rdma_provider_hardware_ready(ready)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/io/rdma_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RDMA provider hardware evidence.
- RDMA provider hardware evidence

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `94f32b0e037cb865a949a21c4e58aa08b961f525f3749d7a115a6395a6a74785`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `94f32b0e037cb865a949a21c4e58aa08b961f525f3749d7a115a6395a6a74785`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `94f32b0e037cb865a949a21c4e58aa08b961f525f3749d7a115a6395a6a74785`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/unit/lib/nogc_async_mut/io/rdma_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/io/rdma_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/io/rdma_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/io/rdma_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
