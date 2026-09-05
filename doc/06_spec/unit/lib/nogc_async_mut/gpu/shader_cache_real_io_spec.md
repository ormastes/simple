# Shader Cache Real Io Specification

> Tests covering Shader cache real I/O.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shader Cache Real Io Specification

## Scenarios

### Shader cache real I/O

#### shader_cache_is_persistent returns true

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- shader_cache_is_persistent returns true
   - Expected: shader_cache_is_persistent() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shader_cache_is_persistent returns true")
expect(shader_cache_is_persistent()).to_equal(true)
```

</details>

#### store and lookup works in memory

- store and lookup works in memory
   - Expected: result.found is true
   - Expected: result.size equals `2048`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("store and lookup works in memory")
shader_cache_store("rio_abc", 2048)
val result = shader_cache_lookup("rio_abc")
expect(result.found).to_equal(true)
expect(result.size).to_equal(2048)
```

</details>

#### store writes file to disk

- store writes file to disk
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("store writes file to disk")
shader_cache_set_directory("/tmp/simple_shader_cache_test")
shader_cache_store("rio_disk01", 512)
val exists = rt_file_exists("/tmp/simple_shader_cache_test/rio_disk01.spv")
expect(exists).to_equal(true)
```

</details>

#### lookup after invalidate falls back to disk

- lookup after invalidate falls back to disk
   - Expected: result.found is true
   - Expected: result.size equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lookup after invalidate falls back to disk")
shader_cache_set_directory("/tmp/simple_shader_cache_test")
shader_cache_store("rio_fallback", 1024)
shader_cache_invalidate("rio_fallback")
val result = shader_cache_lookup("rio_fallback")
expect(result.found).to_equal(true)
expect(result.size).to_equal(1024)
```

</details>

#### set_directory changes cache path

- set_directory changes cache path
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_directory changes cache path")
shader_cache_set_directory("/tmp/simple_shader_cache_alt")
shader_cache_store("rio_alt01", 256)
val exists = rt_file_exists("/tmp/simple_shader_cache_alt/rio_alt01.spv")
expect(exists).to_equal(true)
```

</details>

#### flush writes all entries to disk

- flush writes all entries to disk
   - Expected: e1 is true
   - Expected: e2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flush writes all entries to disk")
shader_cache_set_directory("/tmp/simple_shader_cache_flush")
shader_cache_store("rio_flush01", 100)
shader_cache_store("rio_flush02", 200)
shader_cache_flush()
val e1 = rt_file_exists("/tmp/simple_shader_cache_flush/rio_flush01.spv")
val e2 = rt_file_exists("/tmp/simple_shader_cache_flush/rio_flush02.spv")
expect(e1).to_equal(true)
expect(e2).to_equal(true)
```

</details>

#### hit and miss counts still work

- hit and miss counts still work


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hit and miss counts still work")
val hits_before = shader_cache_hit_count()
val misses_before = shader_cache_miss_count()
shader_cache_store("rio_hitcount", 64)
shader_cache_lookup("rio_hitcount")
shader_cache_lookup("rio_nosuch999")
expect(shader_cache_hit_count()).to_be_greater_than(hits_before)
expect(shader_cache_miss_count()).to_be_greater_than(misses_before)
```

</details>

#### empty hash rejected

- empty hash rejected
   - Expected: shader_cache_size() equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty hash rejected")
val before = shader_cache_size()
shader_cache_store("", 1024)
expect(shader_cache_size()).to_equal(before)
```

</details>

#### zero size rejected

- zero size rejected
   - Expected: shader_cache_size() equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero size rejected")
val before = shader_cache_size()
shader_cache_store("rio_zero", 0)
expect(shader_cache_size()).to_equal(before)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/gpu/shader_cache_real_io_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Shader cache real I/O.
- Shader cache real I/O

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f0b8f0d80e1a513c31637ad97a7f3a2ab239ad60f815ada87f11b59520d2989f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f0b8f0d80e1a513c31637ad97a7f3a2ab239ad60f815ada87f11b59520d2989f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f0b8f0d80e1a513c31637ad97a7f3a2ab239ad60f815ada87f11b59520d2989f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/nogc_async_mut/gpu/shader_cache_real_io_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/gpu/shader_cache_real_io_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/gpu/shader_cache_real_io_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/gpu/shader_cache_real_io_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/gpu/shader_cache_real_io_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/gpu/shader_cache_real_io_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shader_cache_is_persistent returns true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/gpu/shader_cache_real_io_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'store and lookup works in memory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/gpu/shader_cache_real_io_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'store writes file to disk' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
