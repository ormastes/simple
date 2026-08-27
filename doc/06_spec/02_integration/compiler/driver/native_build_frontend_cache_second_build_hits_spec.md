# Native Build Frontend Cache Second Build Hits Specification

> Tests covering native-build front-end cache.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Build Frontend Cache Second Build Hits Specification

## Scenarios

### native-build front-end cache

<details>
<summary>Advanced: misses every module on a cold build and stores one entry each</summary>

#### misses every module on a cold build and stores one entry each _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- misses every module on a cold build and stores one entry each
   - Expected: dir_create_all(root) is true
   - Expected: code equals `0`
   - Expected: line contains `misses=3`
   - Expected: line contains `hits=0`
   - Expected: entry_files(fe_dir).len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("misses every module on a cold build and stores one entry each")
val run_id = getpid()
val root = "build/tmp/fe_cache_spec_{run_id}"
expect(dir_create_all(root)).to_equal(true)
val fe_dir = "{root}/frontend"
val (blob, code) = run_build(FIXTURE_ROOT, "{FIXTURE_ROOT}/main.spl",
    "{root}/cache", fe_dir, "{root}/out1")
expect(code).to_equal(0)
val line = summary_line(blob)
expect(line.contains("misses=3")).to_equal(true)
expect(line.contains("hits=0")).to_equal(true)
expect(entry_files(fe_dir).len()).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: hits every module on an identical second build and parses nothing</summary>

#### hits every module on an identical second build and parses nothing _(slow)_

- hits every module on an identical second build and parses nothing
   - Expected: dir_create_all(root) is true
   - Expected: c1 equals `0`
   - Expected: c2 equals `0`
   - Expected: line contains `hits=3`
   - Expected: line contains `misses=0`
   - Expected: line contains `parses=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("hits every module on an identical second build and parses nothing")
val run_id = getpid()
val root = "build/tmp/fe_cache_hit_spec_{run_id}"
expect(dir_create_all(root)).to_equal(true)
val fe_dir = "{root}/frontend"
val entry = "{FIXTURE_ROOT}/main.spl"
val (_b1, c1) = run_build(FIXTURE_ROOT, entry, "{root}/cache", fe_dir, "{root}/out1")
expect(c1).to_equal(0)
val (b2, c2) = run_build(FIXTURE_ROOT, entry, "{root}/cache", fe_dir, "{root}/out2")
expect(c2).to_equal(0)
val line = summary_line(b2)
expect(line.contains("hits=3")).to_equal(true)
expect(line.contains("misses=0")).to_equal(true)
# The whole point: parse_module_body ran zero times.
expect(line.contains("parses=0")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: produces byte-identical output on a hit and on a miss</summary>

#### produces byte-identical output on a hit and on a miss _(slow)_

- produces byte-identical output on a hit and on a miss
   - Expected: dir_create_all(root) is true
   - Expected: c1 equals `0`
   - Expected: c2 equals `0`
   - Expected: file_exists("{root}/miss.bin") is true
   - Expected: file_exists("{root}/hit.bin") is true
   - Expected: file_read("{root}/hit.bin") equals `file_read("{root}/miss.bin")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("produces byte-identical output on a hit and on a miss")
# A cache that is fast and wrong is worse than no cache. The rebuilt
# ParserModule must drive the same HIR, MIR and codegen, so the emitted
# binary must not differ by one byte.
val run_id = getpid()
val root = "build/tmp/fe_cache_ident_spec_{run_id}"
expect(dir_create_all(root)).to_equal(true)
val entry = "{FIXTURE_ROOT}/main.spl"
val (_b1, c1) = run_build(FIXTURE_ROOT, entry, "{root}/cache1", "{root}/fe", "{root}/miss.bin")
expect(c1).to_equal(0)
# A FRESH object cache dir, so the second build really re-codegens from
# the restored parse instead of reusing the first build's objects.
val (_b2, c2) = run_build(FIXTURE_ROOT, entry, "{root}/cache2", "{root}/fe", "{root}/hit.bin")
expect(c2).to_equal(0)
expect(file_exists("{root}/miss.bin")).to_equal(true)
expect(file_exists("{root}/hit.bin")).to_equal(true)
expect(file_read("{root}/hit.bin")).to_equal(file_read("{root}/miss.bin"))
```

</details>


</details>

<details>
<summary>Advanced: re-parses exactly the edited module and keeps hitting the rest</summary>

#### re-parses exactly the edited module and keeps hitting the rest _(slow)_

- re-parses exactly the edited module and keeps hitting the rest
   - Expected: dir_create_all(src) is true
   - Expected: file_write("{src}/util_a.spl", file_read("{FIXTURE_ROOT}/util_a.spl")) is true
   - Expected: file_write("{src}/util_b.spl", file_read("{FIXTURE_ROOT}/util_b.spl")) is true
   - Expected: file_write("{src}/main.spl", file_read("{FIXTURE_ROOT}/main.spl")) is true
   - Expected: c1 equals `0`
   - Expected: c2 equals `0`
   - Expected: line contains `misses=1`
   - Expected: line contains `hits=2`
   - Expected: line contains `parses=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("re-parses exactly the edited module and keeps hitting the rest")
val run_id = getpid()
val root = "build/tmp/fe_cache_edit_spec_{run_id}"
val src = "{root}/src"
expect(dir_create_all(src)).to_equal(true)
expect(file_write("{src}/util_a.spl", file_read("{FIXTURE_ROOT}/util_a.spl"))).to_equal(true)
expect(file_write("{src}/util_b.spl", file_read("{FIXTURE_ROOT}/util_b.spl"))).to_equal(true)
expect(file_write("{src}/main.spl", file_read("{FIXTURE_ROOT}/main.spl"))).to_equal(true)
val fe_dir = "{root}/frontend"
val entry = "{src}/main.spl"
val (_b1, c1) = run_build(src, entry, "{root}/cache", fe_dir, "{root}/out1")
expect(c1).to_equal(0)
# Touch one module's CONTENT (a comment is enough -- the key is the
# file's sha256, not its mtime, so a no-op rewrite must still hit).
expect(file_write("{src}/util_a.spl",
    file_read("{src}/util_a.spl") + "\n# edited\n")).to_equal(true)
val (b2, c2) = run_build(src, entry, "{root}/cache", fe_dir, "{root}/out2")
expect(c2).to_equal(0)
val line = summary_line(b2)
expect(line.contains("misses=1")).to_equal(true)
expect(line.contains("hits=2")).to_equal(true)
expect(line.contains("parses=1")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: treats a corrupted entry as a miss instead of crashing</summary>

#### treats a corrupted entry as a miss instead of crashing _(slow)_

- treats a corrupted entry as a miss instead of crashing
   - Expected: dir_create_all(root) is true
   - Expected: c1 equals `0`
   - Expected: names.len() equals `3`
   - Expected: file_write(victim, whole.substring(0, whole.len() / 2)) is true
   - Expected: c2 equals `0`
   - Expected: line contains `misses=1`
   - Expected: line contains `hits=2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("treats a corrupted entry as a miss instead of crashing")
# Fail closed is the whole contract: a truncated or garbled entry must
# reparse, never become a module. Truncating mid-blob is the realistic
# shape (a write interrupted by a full disk or a killed build).
val run_id = getpid()
val root = "build/tmp/fe_cache_corrupt_spec_{run_id}"
expect(dir_create_all(root)).to_equal(true)
val fe_dir = "{root}/frontend"
val entry = "{FIXTURE_ROOT}/main.spl"
val (_b1, c1) = run_build(FIXTURE_ROOT, entry, "{root}/cache", fe_dir, "{root}/out1")
expect(c1).to_equal(0)
val names = entry_files(fe_dir)
expect(names.len()).to_equal(3)
val victim = "{fe_dir}/{names[0]}"
val whole = file_read(victim)
expect(file_write(victim, whole.substring(0, whole.len() / 2))).to_equal(true)
val (b2, c2) = run_build(FIXTURE_ROOT, entry, "{root}/cache", fe_dir, "{root}/out2")
expect(c2).to_equal(0)
val line = summary_line(b2)
expect(line.contains("misses=1")).to_equal(true)
expect(line.contains("hits=2")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/driver/native_build_frontend_cache_second_build_hits_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native-build front-end cache.
- native-build front-end cache

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
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

- Canonical SPipe generation for source `ea21f5c996bac0a68e486c672f894a3bd08e675d4bf20c7cfc810cf40de6f314`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea21f5c996bac0a68e486c672f894a3bd08e675d4bf20c7cfc810cf40de6f314`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea21f5c996bac0a68e486c672f894a3bd08e675d4bf20c7cfc810cf40de6f314`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/compiler/driver/native_build_frontend_cache_second_build_hits_spec.spl
mirror: doc/06_spec/02_integration/compiler/driver/native_build_frontend_cache_second_build_hits_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/compiler/driver/native_build_frontend_cache_second_build_hits_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/compiler/driver/native_build_frontend_cache_second_build_hits_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/compiler/driver/native_build_frontend_cache_second_build_hits_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/compiler/driver/native_build_frontend_cache_second_build_hits_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'misses every module on a cold build and stores one entry each' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/compiler/driver/native_build_frontend_cache_second_build_hits_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hits every module on an identical second build and parses nothing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/compiler/driver/native_build_frontend_cache_second_build_hits_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces byte-identical output on a hit and on a miss' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
