# provider_spec

> Verify the pure-Simple GPU provider facade fails closed before dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# provider_spec

Verify the pure-Simple GPU provider facade fails closed before dispatch.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/gpu/provider_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verify the pure-Simple GPU provider facade fails closed before dispatch.

## Scenarios

### typed GPU provider facade

#### should expose every stable ABI status without renumbering

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose every stable ABI status without renumbering
   - Expected: GPU_PROVIDER_STATUS_OK equals `0`
   - Expected: GPU_PROVIDER_STATUS_UNAVAILABLE equals `-1`
   - Expected: GPU_PROVIDER_STATUS_INCOMPATIBLE equals `-2`
   - Expected: GPU_PROVIDER_STATUS_INVALID equals `-3`
   - Expected: GPU_PROVIDER_STATUS_BUSY equals `-4`
   - Expected: GPU_PROVIDER_STATUS_TIMEOUT equals `-5`
   - Expected: GPU_PROVIDER_STATUS_FAILED equals `-6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should expose every stable ABI status without renumbering")
expect(GPU_PROVIDER_STATUS_OK).to_equal(0)
expect(GPU_PROVIDER_STATUS_UNAVAILABLE).to_equal(-1)
expect(GPU_PROVIDER_STATUS_INCOMPATIBLE).to_equal(-2)
expect(GPU_PROVIDER_STATUS_INVALID).to_equal(-3)
expect(GPU_PROVIDER_STATUS_BUSY).to_equal(-4)
expect(GPU_PROVIDER_STATUS_TIMEOUT).to_equal(-5)
expect(GPU_PROVIDER_STATUS_FAILED).to_equal(-6)
```

</details>

#### should reject an unknown backend without acquiring a session

- should reject an unknown backend without acquiring a session
- Query an unsupported backend bit
- Keep every identity and handle unavailable
   - Expected: info.provider_identity equals `0`
   - Expected: info.provider_path equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject an unknown backend without acquiring a session")
step("Query an unsupported backend bit")
val info = gpu_provider_info(8)
var session = gpu_provider_open(8, 0)

step("Keep every identity and handle unavailable")
expect(info.loaded).to_be(false)
expect(info.provider_identity).to_equal(0)
expect(info.provider_path).to_equal("")
expect(session.is_open()).to_be(false)
expect(session.close()).to_be(false)
expect(gpu_provider_unload(8)).to_be(false)
```

</details>

#### should reject invalid resource and submit arguments locally

- should reject invalid resource and submit arguments locally
- Construct the canonical unavailable session
- Return typed non-owning handles
   - Expected: resource.size_bytes equals `0`
- Reject wait and readback without calling a provider
   - Expected: receipt.status equals `GPU_PROVIDER_STATUS_INVALID`
   - Expected: readback.status equals `GPU_PROVIDER_STATUS_INVALID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject invalid resource and submit arguments locally")
step("Construct the canonical unavailable session")
val session = gpu_provider_open(8, 0)
val resource = gpu_provider_resource_alloc(session, 0, 0, 0)
val completion = gpu_provider_submit_raw(session, 1, 0, 0, 1)

step("Return typed non-owning handles")
expect(resource.is_live()).to_be(false)
expect(resource.size_bytes).to_equal(0)
expect(completion.is_live()).to_be(false)

step("Reject wait and readback without calling a provider")
val receipt = gpu_provider_wait(session, completion, 5000000000)
val readback = gpu_provider_readback_raw(session, resource, 0, 0)
expect(receipt.valid).to_be(false)
expect(receipt.status).to_equal(GPU_PROVIDER_STATUS_INVALID)
expect(readback.valid).to_be(false)
expect(readback.status).to_equal(GPU_PROVIDER_STATUS_INVALID)
```

</details>

#### should make duplicate release visibly false

- should make duplicate release visibly false
- Create non-live owned handle wrappers
- Reject release without changing ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should make duplicate release visibly false")
step("Create non-live owned handle wrappers")
var resource = GpuProviderResource(
    backend: GPU_PROVIDER_BACKEND_CUDA,
    session: 0, handle: 0, size_bytes: 0)
var completion = GpuProviderCompletion(
    backend: GPU_PROVIDER_BACKEND_CUDA,
    session: 0, handle: 0, correlation_id: 1)

step("Reject release without changing ownership")
expect(resource.release()).to_be(false)
expect(completion.release()).to_be(false)
expect(resource.is_live()).to_be(false)
expect(completion.is_live()).to_be(false)
```

</details>

#### should reject cross-session handles before provider dispatch

- should reject cross-session handles before provider dispatch
- Create two distinct live-looking sessions
- Reject both ownership mismatches locally
   - Expected: receipt.status equals `GPU_PROVIDER_STATUS_INVALID`
   - Expected: readback.status equals `GPU_PROVIDER_STATUS_INVALID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject cross-session handles before provider dispatch")
step("Create two distinct live-looking sessions")
val session = GpuProviderSession(
    backend: GPU_PROVIDER_BACKEND_VULKAN, handle: 101)
val foreign_completion = GpuProviderCompletion(
    backend: GPU_PROVIDER_BACKEND_VULKAN,
    session: 202, handle: 303, correlation_id: 9)
val foreign_resource = GpuProviderResource(
    backend: GPU_PROVIDER_BACKEND_VULKAN,
    session: 202, handle: 404, size_bytes: 64)

step("Reject both ownership mismatches locally")
val receipt = gpu_provider_wait(
    session, foreign_completion, 5000000000)
val readback = gpu_provider_readback_raw(
    session, foreign_resource, 1, 64)
expect(receipt.valid).to_be(false)
expect(receipt.status).to_equal(GPU_PROVIDER_STATUS_INVALID)
expect(readback.valid).to_be(false)
expect(readback.status).to_equal(GPU_PROVIDER_STATUS_INVALID)
```

</details>

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `05e475789e3bcd31b73c92d63da57fe99fb6d1902dab2c56cef080b93d5bc5f9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `05e475789e3bcd31b73c92d63da57fe99fb6d1902dab2c56cef080b93d5bc5f9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `05e475789e3bcd31b73c92d63da57fe99fb6d1902dab2c56cef080b93d5bc5f9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/01_unit/lib/nogc_sync_mut/gpu/provider_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/gpu/provider_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=75 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/gpu/provider_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/gpu/provider_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/gpu/provider_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/gpu/provider_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose every stable ABI status without renumbering' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_sync_mut/gpu/provider_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose every stable ABI status without renumbering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/gpu/provider_spec.spl:29:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject an unknown backend without acquiring a session' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_sync_mut/gpu/provider_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject an unknown backend without acquiring a session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/gpu/provider_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject invalid resource and submit arguments locally' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_sync_mut/gpu/provider_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject invalid resource and submit arguments locally' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/gpu/provider_spec.spl:65:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should make duplicate release visibly false' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_sync_mut/gpu/provider_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject cross-session handles before provider dispatch' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
