# Native Build Hir Streaming Sharding Specification

> Tests covering native-build HIR sharding on the streaming-surfaces path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Build Hir Streaming Sharding Specification

## Scenarios

### native-build HIR sharding on the streaming-surfaces path

<details>
<summary>Advanced: shards and caches HIR on the streaming-surfaces (bootstrap stage3) path too, byte-identically</summary>

#### shards and caches HIR on the streaming-surfaces (bootstrap stage3) path too, byte-identically _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- shards and caches HIR on the streaming-surfaces (bootstrap stage3) path too, byte-identically
   - Expected: dir_create_all(root) is true
   - Expected: code equals `0`
   - Expected: cb equals `0`
   - Expected: count_of(blob, "[hir-shard] done shard=") equals `2`
   - Expected: sum_field(blob, "[hir-shard] done shard=", "lowered=") equals `3`
   - Expected: summary contains `hits=3`
   - Expected: summary contains `misses=0`
   - Expected: file_read("{root}/sharded.bin") equals `file_read("{root}/plain.bin")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("shards and caches HIR on the streaming-surfaces (bootstrap stage3) path too, byte-identically")
# SIMPLE_STAGE3_STREAMING_SURFACES=1 + SIMPLE_BOOTSTRAP=1 selects
# lower_and_check_streaming_surfaces_impl, the path the scripted
# stage3/stage4 builds take. Its surfaces are frozen in full before
# the HIR loop, so the same whole-closure digest key is sound there.
val run_id = getpid()
val root = "build/tmp/hir_shard_stream_spec_{run_id}"
expect(dir_create_all(root)).to_equal(true)
rt_env_set("SIMPLE_BOOTSTRAP", "1")
rt_env_set("SIMPLE_STAGE3_STREAMING_SURFACES", "1")
val (blob, code) = run_build("{root}/c1", "{root}/fe", "{root}/hir", "{root}/sharded.bin", "2", "1")
val (_b, cb) = run_build("{root}/c2", "{root}/fe2", "{root}/hir2", "{root}/plain.bin", "1", "0")
rt_env_set("SIMPLE_BOOTSTRAP", "")
rt_env_set("SIMPLE_STAGE3_STREAMING_SURFACES", "")
expect(code).to_equal(0)
expect(cb).to_equal(0)
expect(count_of(blob, "[hir-shard] done shard=")).to_equal(2)
expect(sum_field(blob, "[hir-shard] done shard=", "lowered=")).to_equal(3)
val summary = last_line_with(blob, "[hir-cache]")
expect(summary.contains("hits=3")).to_equal(true)
expect(summary.contains("misses=0")).to_equal(true)
expect(file_read("{root}/sharded.bin")).to_equal(file_read("{root}/plain.bin"))
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/driver/native_build_hir_streaming_sharding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native-build HIR sharding on the streaming-surfaces path.
- native-build HIR sharding on the streaming-surfaces path

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7ef6f283eb3a9cdca0b707bad45bc2e54abc8163e8c72a06fd55d263d86fe471`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7ef6f283eb3a9cdca0b707bad45bc2e54abc8163e8c72a06fd55d263d86fe471`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7ef6f283eb3a9cdca0b707bad45bc2e54abc8163e8c72a06fd55d263d86fe471`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/02_integration/compiler/driver/native_build_hir_streaming_sharding_spec.spl
mirror: doc/06_spec/02_integration/compiler/driver/native_build_hir_streaming_sharding_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/compiler/driver/native_build_hir_streaming_sharding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/compiler/driver/native_build_hir_streaming_sharding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/compiler/driver/native_build_hir_streaming_sharding_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/compiler/driver/native_build_hir_streaming_sharding_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shards and caches HIR on the streaming-surfaces (bootstrap stage3) path too, byte-identically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
