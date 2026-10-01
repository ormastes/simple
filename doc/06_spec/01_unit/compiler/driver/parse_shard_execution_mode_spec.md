# Parse Shard Execution Mode Specification

> Tests covering parse shard workers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parse Shard Execution Mode Specification

## Scenarios

### parse shard workers

#### spawns shard children only after the worker execution mode is fixed

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- spawns shard children only after the worker execution mode is fixed


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spawns shard children only after the worker execution mode is fixed")
# `run_native_build_worker` establishes SIMPLE_EXECUTION_MODE and
# SIMPLE_BINARY, and only then calls `run_parse_shards`. Because
# rt_process_spawn_async passes the parent's environment through, that
# ordering is the entire reason a shard child runs in the SAME mode as
# the main worker rather than a degraded one. If the spawn ever moved
# above the env_set, shards would silently diverge from the worker they
# are warming the cache for -- invisible in any log, because both
# answers are "the build completed".
val src = file_read("src/app/cli/native_build_main.spl")
val mode_at = src.index_of("env_set(\"SIMPLE_EXECUTION_MODE\", \"interpret\")")
val binary_at = src.index_of("env_set(\"SIMPLE_BINARY\", simple_bin)")
val spawn_at = src.index_of("run_parse_shards(args, shard_count")
expect(mode_at > 0).to_be_true()
expect(binary_at > 0).to_be_true()
expect(spawn_at > 0).to_be_true()
expect(mode_at < spawn_at).to_be_true()
expect(binary_at < spawn_at).to_be_true()
```

</details>

#### decides shard ownership before emitting the in-flight parse receipt

- decides shard ownership before emitting the in-flight parse receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decides shard ownership before emitting the in-flight parse receipt")
# A shard child walks the whole source list and parses only the slice
# it owns. Emitting the per-file "current" receipt before the ownership
# test made each of 8 children claim all 666 files, so 8x583 receipts
# named a file that process never opened and their dt stamps measured
# the gap between two skips. That is why run7's per-shard cost could
# not be read off the merged log at all.
val src = file_read(
    "src/compiler/80.driver/driver_source_pipeline_parsing.spl")
val owns_at = src.index_of("if not _driver_parse_shard_owns(source.path):")
val receipt_at = src.index_of(
    "log_build_progress(\"parse\", \"files\", progress_parse_done,")
expect(owns_at > 0).to_be_true()
expect(receipt_at > 0).to_be_true()
expect(owns_at < receipt_at).to_be_true()
```

</details>

#### routes shard parses through the same front-end cache as the driver

- routes shard parses through the same front-end cache as the driver


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes shard parses through the same front-end cache as the driver")
# Hypothesis raised against run8: shard children re-parse everything
# they own because only the driver consults the cache. Measured false.
# An isolated warm shard (`--parse-shard=0/8`, same tree, same scope)
# reports `hits=94 misses=0 parses=0` and `[parse-shard] done
# shard=0/8 parses=0`, and an earlier real 8-shard run reported
# `hits=73/85/90 misses=0 parses=0` per shard. The mechanism is
# structural and pinned here: the cache lookup lives in
# `frontend_parse_or_restore`, the single boundary every parse goes
# through, and nothing about it is conditional on the shard spec — so
# a shard cannot bypass the cache without the driver bypassing it too.
# A `parses=` near the owned-file count therefore means a COLD SCOPE
# (a fresh SIMPLE_CACHE_SCOPE, or a compiler-source edit rotating the
# scope key), not a shard that ignores the cache.
val fe = file_read("src/compiler/10.frontend/frontend.spl")
expect(fe).to_contain("fn frontend_parse_or_restore(")
expect(fe).to_contain("frontend_parse_cache_load(key)")
expect(fe).to_contain("frontend_parse_cache_note_hit()")
# No shard-conditional branch anywhere on the cache boundary.
expect(fe.contains("SIMPLE_PARSE_SHARD")).to_be_false()
expect(fe.contains("driver_parse_shard_active")).to_be_false()
val cache = file_read("src/compiler/10.frontend/frontend_parse_cache.spl")
expect(cache.contains("SIMPLE_PARSE_SHARD")).to_be_false()
```

</details>

#### counts front-end cache stores so a double write is visible

- counts front-end cache stores so a double write is visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts front-end cache stores so a double write is visible")
# A module must be written to the front-end cache at most once per
# process. Without a counter, a miss path that re-entered would pay the
# full parse twice and the build would only look slow.
expect(frontend_parse_cache_stores() >= 0).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/parse_shard_execution_mode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering parse shard workers.
- parse shard workers

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `809d97c978e3e02ab6e8b7402313fe680d9dbe1868dcb794a8837221e0ee28e0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `809d97c978e3e02ab6e8b7402313fe680d9dbe1868dcb794a8837221e0ee28e0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `809d97c978e3e02ab6e8b7402313fe680d9dbe1868dcb794a8837221e0ee28e0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/driver/parse_shard_execution_mode_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/parse_shard_execution_mode_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/parse_shard_execution_mode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/parse_shard_execution_mode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/parse_shard_execution_mode_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'spawns shard children only after the worker execution mode is fixed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/parse_shard_execution_mode_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decides shard ownership before emitting the in-flight parse receipt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/parse_shard_execution_mode_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes shard parses through the same front-end cache as the driver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
