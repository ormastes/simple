# Native Build Hir Sharding Specification

> Tests covering native-build HIR sharding.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Build Hir Sharding Specification

## Scenarios

### native-build HIR sharding

<details>
<summary>Advanced: lowers every module in exactly one HIR shard process and the real build loads them all</summary>

#### lowers every module in exactly one HIR shard process and the real build loads them all _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lowers every module in exactly one HIR shard process and the real build loads them all
   - Expected: dir_create_all(root) is true
   - Expected: code equals `0`
   - Expected: blob contains `[hir-shard] 2/2 shard(s) completed split=queue`
   - Expected: count_of(blob, "[hir-shard] done shard=") equals `2`
   - Expected: sum_field(blob, "[hir-shard] done shard=", "lowered=") equals `3`
   - Expected: sum_field(blob, "[hir-shard] done shard=", "claimed=") equals `3`
   - Expected: last_line_with(blob, "[hir-shard] done shard=") contains `levels=2`
   - Expected: summary contains `hits=3`
   - Expected: summary contains `misses=0`
   - Expected: summary contains `stores=0`
   - Expected: count_of(blob, "[frontend-cache] hits=3 misses=0 parses=0") equals `3`
   - Expected: file_exists("{root}/hir/.lock") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("lowers every module in exactly one HIR shard process and the real build loads them all")
val run_id = getpid()
val root = "build/tmp/hir_shard_spec_{run_id}"
expect(dir_create_all(root)).to_equal(true)
val (blob, code) = run_build("{root}/cache", "{root}/fe", "{root}/hir", "{root}/out", "2", "1")
expect(code).to_equal(0)
# N workers ran and each reported.
expect(blob.contains("[hir-shard] 2/2 shard(s) completed split=queue")).to_equal(true)
expect(count_of(blob, "[hir-shard] done shard=")).to_equal(2)
# Every module lowered and stored by exactly one shard: a double
# claim overshoots 3, a lost one undershoots, a shard that silently
# fell back to "own nothing" contributes 0 to both sums.
expect(sum_field(blob, "[hir-shard] done shard=", "lowered=")).to_equal(3)
expect(sum_field(blob, "[hir-shard] done shard=", "claimed=")).to_equal(3)
# Dependency levels were computed (main imports util_a/util_b: 2 levels).
expect(last_line_with(blob, "[hir-shard] done shard=").contains("levels=2")).to_equal(true)
# The REAL build's HIR phase was all hits and lowered nothing.
val summary = last_line_with(blob, "[hir-cache]")
expect(summary.contains("hits=3")).to_equal(true)
expect(summary.contains("misses=0")).to_equal(true)
expect(summary.contains("stores=0")).to_equal(true)
# Every HIR shard child AND the real build restored every module from
# the front-end cache the parse shards wrote: 2 children + 1 real build,
# each hits=3 misses=0 parses=0. Pre-fix (parse_shard_main.spl and
# native_build_worker.spl hashed to different "exe=" identities) the
# HIR children ran hits=0 misses=3 parses=3 -- re-parsing the whole
# closure from source before lowering anything -- and only the real
# build hit, so this count was 1.
expect(count_of(blob, "[frontend-cache] hits=3 misses=0 parses=0")).to_equal(3)
# The queue dir is private to the orchestrator and removed with it.
expect(file_exists("{root}/hir/.lock")).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: produces a binary byte-identical to an unsharded, uncached --threads 1 build</summary>

#### produces a binary byte-identical to an unsharded, uncached --threads 1 build _(slow)_

- produces a binary byte-identical to an unsharded, uncached --threads 1 build
   - Expected: dir_create_all(root) is true
   - Expected: ca equals `0`
   - Expected: cb equals `0`
   - Expected: file_exists("{root}/sharded.bin") is true
   - Expected: file_exists("{root}/plain.bin") is true
   - Expected: file_read("{root}/sharded.bin") equals `file_read("{root}/plain.bin")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("produces a binary byte-identical to an unsharded, uncached --threads 1 build")
# Sharding may only change WHICH PROCESS lowered a module. The real
# build runs MIR/codegen from DECODED modules, so identical bytes here
# is the proof that the codec reproduces what MIR needs.
val run_id = getpid()
val root = "build/tmp/hir_shard_ident_spec_{run_id}"
expect(dir_create_all(root)).to_equal(true)
val (_a, ca) = run_build("{root}/c1", "{root}/fe", "{root}/hir", "{root}/sharded.bin", "2", "1")
expect(ca).to_equal(0)
val (_b, cb) = run_build("{root}/c2", "{root}/fe2", "{root}/hir2", "{root}/plain.bin", "1", "0")
expect(cb).to_equal(0)
expect(file_exists("{root}/sharded.bin")).to_equal(true)
expect(file_exists("{root}/plain.bin")).to_equal(true)
expect(file_read("{root}/sharded.bin")).to_equal(file_read("{root}/plain.bin"))
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/integration/compiler/driver/native_build_hir_sharding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native-build HIR sharding.
- native-build HIR sharding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 2 |
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

- Canonical SPipe generation for source `a637da8ccd0409ea1da125eea5bc3b085a91e2fce4298d3937d093beb61e1141`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a637da8ccd0409ea1da125eea5bc3b085a91e2fce4298d3937d093beb61e1141`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a637da8ccd0409ea1da125eea5bc3b085a91e2fce4298d3937d093beb61e1141`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/compiler/driver/native_build_hir_sharding_spec.spl
mirror: doc/06_spec/integration/compiler/driver/native_build_hir_sharding_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/compiler/driver/native_build_hir_sharding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/compiler/driver/native_build_hir_sharding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/compiler/driver/native_build_hir_sharding_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/compiler/driver/native_build_hir_sharding_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers every module in exactly one HIR shard process and the real build loads them all' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/driver/native_build_hir_sharding_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces a binary byte-identical to an unsharded, uncached --threads 1 build' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
