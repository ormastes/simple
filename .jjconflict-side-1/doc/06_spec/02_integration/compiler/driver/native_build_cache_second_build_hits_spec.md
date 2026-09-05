# Native Build Cache Second Build Hits Specification

> Tests covering native-build object cache.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Build Cache Second Build Hits Specification

## Scenarios

### native-build object cache

<details>
<summary>Advanced: persists per-module entries so a second identical build hits</summary>

#### persists per-module entries so a second identical build hits _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- persists per-module entries so a second identical build hits
   - Expected: dir_create_all(root) is true
   - Expected: first equals `0`
   - Expected: file_exists(cache_file) is true
   - Expected: count_rows(after_first, "source: \"") equals `3`
   - Expected: after_first contains `util_a.spl`
   - Expected: second equals `0`
   - Expected: file_exists("{root}/out2") is true
   - Expected: count_rows(file_read(cache_file), "source: \"") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("persists per-module entries so a second identical build hits")
val run_id = getpid()
val root = "build/tmp/native_build_cache_spec_{run_id}"
val cache_dir = "{root}/cache"
expect(dir_create_all(root)).to_equal(true)
val entry = "{FIXTURE_ROOT}/main.spl"
val first = cli_native_build(build_args(FIXTURE_ROOT, entry, cache_dir, "{root}/out1"))
expect(first).to_equal(0)
val cache_file = "{cache_dir}/build_cache.sdn"
expect(file_exists(cache_file)).to_equal(true)
val after_first = file_read(cache_file)
expect(count_rows(after_first, "source: \"")).to_equal(3)
expect(after_first.contains("util_a.spl")).to_equal(true)
val second = cli_native_build(build_args(FIXTURE_ROOT, entry, cache_dir, "{root}/out2"))
expect(second).to_equal(0)
expect(file_exists("{root}/out2")).to_equal(true)
expect(count_rows(file_read(cache_file), "source: \"")).to_equal(3)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/driver/native_build_cache_second_build_hits_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native-build object cache.
- native-build object cache

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

- Canonical SPipe generation for source `e1170a28d4c68497c02b4f0dee9b90e76b6145c5338b2aca5c57fabdcad845ce`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e1170a28d4c68497c02b4f0dee9b90e76b6145c5338b2aca5c57fabdcad845ce`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e1170a28d4c68497c02b4f0dee9b90e76b6145c5338b2aca5c57fabdcad845ce`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/02_integration/compiler/driver/native_build_cache_second_build_hits_spec.spl
mirror: doc/06_spec/02_integration/compiler/driver/native_build_cache_second_build_hits_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/compiler/driver/native_build_cache_second_build_hits_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/compiler/driver/native_build_cache_second_build_hits_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/compiler/driver/native_build_cache_second_build_hits_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/compiler/driver/native_build_cache_second_build_hits_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'persists per-module entries so a second identical build hits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
