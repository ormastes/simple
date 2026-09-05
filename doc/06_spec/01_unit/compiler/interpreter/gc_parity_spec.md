# Gc Parity Specification

> Tests covering Interpreter GC Parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Parity Specification

## Scenarios

### Interpreter GC Parity

#### family extraction from resolved path

#### extracts nogc_sync_mut from path

- extracts nogc_sync_mut from path
   - Expected: family equals `nogc_sync_mut`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts nogc_sync_mut from path")
val path = "src/lib/nogc_sync_mut/fs.spl"
val family = _extract_family(path)
expect(family).to_equal("nogc_sync_mut")
```

</details>

#### extracts nogc_async_mut from path

- extracts nogc_async_mut from path
   - Expected: family equals `nogc_async_mut`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts nogc_async_mut from path")
val path = "src/lib/nogc_async_mut/thread.spl"
val family = _extract_family(path)
expect(family).to_equal("nogc_async_mut")
```

</details>

#### extracts gc_async_mut from path

- extracts gc_async_mut from path
   - Expected: family equals `gc_async_mut`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts gc_async_mut from path")
val path = "src/lib/gc_async_mut/cuda.spl"
val family = _extract_family(path)
expect(family).to_equal("gc_async_mut")
```

</details>

#### extracts nogc_async_immut from path

- extracts nogc_async_immut from path
   - Expected: family equals `nogc_async_immut`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts nogc_async_immut from path")
val path = "src/lib/nogc_async_immut/persistent.spl"
val family = _extract_family(path)
expect(family).to_equal("nogc_async_immut")
```

</details>

#### extracts common from path

- extracts common from path
   - Expected: family equals `common`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts common from path")
val path = "src/lib/common/text.spl"
val family = _extract_family(path)
expect(family).to_equal("common")
```

</details>

#### extracts nogc_async_mut_noalloc before nogc_async_mut

- extracts nogc_async_mut_noalloc before nogc_async_mut
   - Expected: family equals `nogc_async_mut_noalloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts nogc_async_mut_noalloc before nogc_async_mut")
val path = "src/lib/nogc_async_mut_noalloc/memory.spl"
val family = _extract_family(path)
expect(family).to_equal("nogc_async_mut_noalloc")
```

</details>

#### returns empty for unknown path

- returns empty for unknown path
   - Expected: family equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for unknown path")
val path = "src/app/cli/main.spl"
val family = _extract_family(path)
expect(family).to_equal("")
```

</details>

#### is_nogc_family classification

#### nogc_sync_mut is nogc

- nogc_sync_mut is nogc
   - Expected: _is_nogc("nogc_sync_mut") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nogc_sync_mut is nogc")
expect(_is_nogc("nogc_sync_mut")).to_equal(true)
```

</details>

#### nogc_async_mut is nogc

- nogc_async_mut is nogc
   - Expected: _is_nogc("nogc_async_mut") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nogc_async_mut is nogc")
expect(_is_nogc("nogc_async_mut")).to_equal(true)
```

</details>

#### nogc_async_mut_noalloc is nogc

- nogc_async_mut_noalloc is nogc
   - Expected: _is_nogc("nogc_async_mut_noalloc") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nogc_async_mut_noalloc is nogc")
expect(_is_nogc("nogc_async_mut_noalloc")).to_equal(true)
```

</details>

#### gc_async_mut is not nogc

- gc_async_mut is not nogc
   - Expected: _is_nogc("gc_async_mut") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gc_async_mut is not nogc")
expect(_is_nogc("gc_async_mut")).to_equal(false)
```

</details>

#### common is not nogc

- common is not nogc
   - Expected: _is_nogc("common") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("common is not nogc")
expect(_is_nogc("common")).to_equal(false)
```

</details>

#### is_gc_family classification

#### gc_async_mut is gc

- gc_async_mut is gc
   - Expected: _is_gc("gc_async_mut") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gc_async_mut is gc")
expect(_is_gc("gc_async_mut")).to_equal(true)
```

</details>

#### nogc_sync_mut is not gc

- nogc_sync_mut is not gc
   - Expected: _is_gc("nogc_sync_mut") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nogc_sync_mut is not gc")
expect(_is_gc("nogc_sync_mut")).to_equal(false)
```

</details>

#### common is not gc

- common is not gc
   - Expected: _is_gc("common") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("common is not gc")
expect(_is_gc("common")).to_equal(false)
```

</details>

#### is_noalloc_family classification

#### nogc_async_mut_noalloc is noalloc

- nogc_async_mut_noalloc is noalloc
   - Expected: _is_noalloc("nogc_async_mut_noalloc") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nogc_async_mut_noalloc is noalloc")
expect(_is_noalloc("nogc_async_mut_noalloc")).to_equal(true)
```

</details>

#### nogc_sync_mut is not noalloc

- nogc_sync_mut is not noalloc
   - Expected: _is_noalloc("nogc_sync_mut") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nogc_sync_mut is not noalloc")
expect(_is_noalloc("nogc_sync_mut")).to_equal(false)
```

</details>

#### gc_async_mut is not noalloc

- gc_async_mut is not noalloc
   - Expected: _is_noalloc("gc_async_mut") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gc_async_mut is not noalloc")
expect(_is_noalloc("gc_async_mut")).to_equal(false)
```

</details>

#### should_warn_gc_boundary

#### warns when nogc imports gc

- warns when nogc imports gc
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns when nogc imports gc")
val result = _should_warn("nogc_sync_mut", "gc_async_mut")
expect(result).to_equal(true)
```

</details>

#### warns when nogc_async imports gc

- warns when nogc_async imports gc
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns when nogc_async imports gc")
val result = _should_warn("nogc_async_mut", "gc_async_mut")
expect(result).to_equal(true)
```

</details>

#### does not warn when gc imports nogc

- does not warn when gc imports nogc
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not warn when gc imports nogc")
val result = _should_warn("gc_async_mut", "nogc_sync_mut")
expect(result).to_equal(false)
```

</details>

#### does not warn for same family

- does not warn for same family
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not warn for same family")
val result = _should_warn("nogc_sync_mut", "nogc_sync_mut")
expect(result).to_equal(false)
```

</details>

#### does not warn when common imports anything

- does not warn when common imports anything
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not warn when common imports anything")
val result = _should_warn("common", "gc_async_mut")
expect(result).to_equal(false)
```

</details>

#### does not warn when anything imports common

- does not warn when anything imports common
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not warn when anything imports common")
val result = _should_warn("nogc_sync_mut", "common")
expect(result).to_equal(false)
```

</details>

#### warns when noalloc imports allocating nogc

- warns when noalloc imports allocating nogc
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns when noalloc imports allocating nogc")
val result = _should_warn_noalloc("nogc_async_mut_noalloc", "nogc_sync_mut")
expect(result).to_equal(true)
```

</details>

#### warns when noalloc imports gc

- warns when noalloc imports gc
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns when noalloc imports gc")
val result = _should_warn_noalloc("nogc_async_mut_noalloc", "gc_async_mut")
expect(result).to_equal(true)
```

</details>

#### does not warn for noalloc importing common

- does not warn for noalloc importing common
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not warn for noalloc importing common")
val result = _should_warn_noalloc("nogc_async_mut_noalloc", "common")
expect(result).to_equal(false)
```

</details>

#### interpreter vs compiler family detection consistency

#### both detect nogc_sync_mut as nogc

- both detect nogc_sync_mut as nogc
   - Expected: _is_nogc(path_family) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("both detect nogc_sync_mut as nogc")
val path_family = _extract_family("src/lib/nogc_sync_mut/fs.spl")
expect(_is_nogc(path_family)).to_equal(true)
```

</details>

#### both detect gc_async_mut as gc

- both detect gc_async_mut as gc
   - Expected: _is_gc(path_family) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("both detect gc_async_mut as gc")
val path_family = _extract_family("src/lib/gc_async_mut/cuda.spl")
expect(_is_gc(path_family)).to_equal(true)
```

</details>

#### both detect noalloc correctly

- both detect noalloc correctly
   - Expected: _is_noalloc(path_family) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("both detect noalloc correctly")
val path_family = _extract_family("src/lib/nogc_async_mut_noalloc/mem.spl")
expect(_is_noalloc(path_family)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/gc_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Interpreter GC Parity.
- Interpreter GC Parity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
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

- Canonical SPipe generation for source `ec420e0a5a32df3dd8fd8b7e3ec14101fda34a0096a826c45f4c257d0eb8862a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ec420e0a5a32df3dd8fd8b7e3ec14101fda34a0096a826c45f4c257d0eb8862a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ec420e0a5a32df3dd8fd8b7e3ec14101fda34a0096a826c45f4c257d0eb8862a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interpreter/gc_parity_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/gc_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/gc_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/gc_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/gc_parity_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts nogc_sync_mut from path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/gc_parity_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts nogc_async_mut from path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/gc_parity_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts gc_async_mut from path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
