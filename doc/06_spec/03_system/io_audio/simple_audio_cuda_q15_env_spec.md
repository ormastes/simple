# simple_audio_cuda_q15_env_spec

> Native CUDA audio execution evidence; unavailable hosts report an explicit gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_audio_cuda_q15_env_spec

Native CUDA audio execution evidence; unavailable hosts report an explicit gate.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/io_audio/simple_audio_cuda_q15_env_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Native CUDA audio execution evidence; unavailable hosts report an explicit gate.

## Scenarios

### Simple audio CUDA Q15 environment

#### env_skip: CUDA audio execution not requested or unavailable

- env_skip: CUDA audio execution not requested or unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("env_skip: CUDA audio execution not requested or unavailable")
expect(test_env_gate_skip("SIMPLE_CUDA_TEST")).to_contain("Skipped")
```

</details>

#### runs convolution on CUDA and proves device readback parity

- runs convolution on CUDA and proves device readback parity
   - Expected: result.completed is true
   - Expected: result.reason equals `device-readback`
   - Expected: result.readback_count equals `4`
   - Expected: result.readback_sample(0) equals `16384`
   - Expected: result.readback_sample(1) equals `16384`
   - Expected: result.readback_sample(2) equals `0`
   - Expected: result.readback_sample(3) equals `-2048`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs convolution on CUDA and proves device readback parity")
var executor = SimpleAudioCudaQ15Executor.create()
val result = simple_audio_q15_execute_cuda(executor, [32768u32, 16384u32, 4294959104u32], [16384u32, 8192u32])
expect(result.completed).to_equal(true)
expect(result.reason).to_equal("device-readback")
expect(result.backend_handle).to_be_greater_than(0)
expect(result.device_identity).to_be_greater_than(0)
expect(result.readback_checksum).to_be_greater_than(0)
expect(result.normalized_error_millionths).to_be_less_than(11)
expect(result.readback_count).to_equal(4)
expect(result.readback_sample(0)).to_equal(16384)
expect(result.readback_sample(1)).to_equal(16384)
expect(result.readback_sample(2)).to_equal(0)
expect(result.readback_sample(3)).to_equal(-2048)
result.release_readback()
executor.shutdown()
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-004`
- `REQ-005`
- `REQ-007`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `46dd017c98400d02041497315462f5b748bcc84b976d58e9c334ac9fca594313`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `46dd017c98400d02041497315462f5b748bcc84b976d58e9c334ac9fca594313`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `46dd017c98400d02041497315462f5b748bcc84b976d58e9c334ac9fca594313`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/io_audio/simple_audio_cuda_q15_env_spec.spl
mirror: doc/06_spec/03_system/io_audio/simple_audio_cuda_q15_env_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/io_audio/simple_audio_cuda_q15_env_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/io_audio/simple_audio_cuda_q15_env_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/io_audio/simple_audio_cuda_q15_env_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/io_audio/simple_audio_cuda_q15_env_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/io_audio/simple_audio_cuda_q15_env_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'env_skip: CUDA audio execution not requested or unavailable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/io_audio/simple_audio_cuda_q15_env_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs convolution on CUDA and proves device readback parity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
