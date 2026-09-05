# cuda_web_layout_receipt_spec

> Verify CUDA web-layout proof conversion without fabricated provenance.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cuda_web_layout_receipt_spec

Verify CUDA web-layout proof conversion without fabricated provenance.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/web_db_offload/cuda_web_layout_receipt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verify CUDA web-layout proof conversion without fabricated provenance.

## Scenarios

### CUDA web layout device receipt

#### should preserve exact device provenance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should preserve exact device provenance
- Convert a complete CUDA layout proof
- Require every production receipt invariant
   - Expected: receipt.backend_handle equals `73`
   - Expected: receipt.device_identity equals `9001`
   - Expected: receipt.actual_checksum equals `123456`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should preserve exact device provenance")
step("Convert a complete CUDA layout proof")
val receipt = web_cuda_layout_device_receipt(exact_cuda_web_proof())

step("Require every production receipt invariant")
expect(gpu_wdb_device_receipt_valid(receipt)).to_be(true)
expect(receipt.backend_handle).to_equal(73)
expect(receipt.device_identity).to_equal(9001)
expect(receipt.actual_checksum).to_equal(123456)
```

</details>

#### should reject CPU-oracle mismatch without hiding its checksum

- should reject CPU-oracle mismatch without hiding its checksum
- Corrupt an otherwise complete layout proof
- Fail closed with retained mismatch evidence
   - Expected: gpu_wdb_device_receipt_reason(receipt) equals `device-not-completed`
   - Expected: receipt.expected_checksum equals `123456`
   - Expected: receipt.actual_checksum equals `123455`
   - Expected: receipt.mismatch_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject CPU-oracle mismatch without hiding its checksum")
step("Corrupt an otherwise complete layout proof")
var proof = exact_cuda_web_proof()
proof.oracle_verified = false
proof.actual_checksum = 123455
proof.mismatch_count = 1
val receipt = web_cuda_layout_device_receipt(proof)

step("Fail closed with retained mismatch evidence")
expect(gpu_wdb_device_receipt_valid(receipt)).to_be(false)
expect(gpu_wdb_device_receipt_reason(receipt)).to_equal("device-not-completed")
expect(receipt.expected_checksum).to_equal(123456)
expect(receipt.actual_checksum).to_equal(123455)
expect(receipt.mismatch_count).to_equal(1)
```

</details>

#### should reject a CPU backend carrying copied device-looking fields

- should reject a CPU backend carrying copied device-looking fields
- Change only the executed backend identity
- Refuse synthetic cross-backend promotion


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject a CPU backend carrying copied device-looking fields")
step("Change only the executed backend identity")
var proof = exact_cuda_web_proof()
proof.executed_backend = "serial_cpu"
val receipt = web_cuda_layout_device_receipt(proof)

step("Refuse synthetic cross-backend promotion")
expect(gpu_wdb_device_receipt_valid(receipt)).to_be(false)
expect(receipt.completed).to_be(false)
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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e8d8debfd1df8ab3d254ebafed83849c83be0fe3ab4b20ee6c38363256925e1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e8d8debfd1df8ab3d254ebafed83849c83be0fe3ab4b20ee6c38363256925e1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e8d8debfd1df8ab3d254ebafed83849c83be0fe3ab4b20ee6c38363256925e1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/01_unit/lib/gc_async_mut/web_db_offload/cuda_web_layout_receipt_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/web_db_offload/cuda_web_layout_receipt_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/web_db_offload/cuda_web_layout_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/web_db_offload/cuda_web_layout_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/web_db_offload/cuda_web_layout_receipt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/web_db_offload/cuda_web_layout_receipt_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve exact device provenance' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/web_db_offload/cuda_web_layout_receipt_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve exact device provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/web_db_offload/cuda_web_layout_receipt_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject CPU-oracle mismatch without hiding its checksum' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/web_db_offload/cuda_web_layout_receipt_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject CPU-oracle mismatch without hiding its checksum' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/web_db_offload/cuda_web_layout_receipt_spec.spl:77:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a CPU backend carrying copied device-looking fields' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/web_db_offload/cuda_web_layout_receipt_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a CPU backend carrying copied device-looking fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
