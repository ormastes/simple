# runtime_family_spec

> Purpose: This spec proves Runtime Family Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# runtime_family_spec

Purpose: This spec proves Runtime Family Integration.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/runtime_family_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves Runtime Family Integration.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### Runtime Family Integration

#### target preset — baremetal

#### baremetal allowed families has exactly two entries

- baremetal allowed families has exactly two entries
   - Expected: families.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RUNTIMEFAMILY-001
# @req: REQ-RUNTIMEFAMILY-001
step("baremetal allowed families has exactly two entries")
val families = baremetal_allowed_families()
expect(families.len()).to_equal(2)
```

</details>

#### baremetal allowed families contains nogc_async_mut_noalloc

- baremetal allowed families contains nogc_async_mut_noalloc
- baremetal allowed families contains nogc_async_mut_noalloc
   - Expected: families[0] equals `nogc_async_mut_noalloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("baremetal allowed families contains nogc_async_mut_noalloc")
step("baremetal allowed families contains nogc_async_mut_noalloc")
val families = baremetal_allowed_families()
expect(families[0]).to_equal("nogc_async_mut_noalloc")
```

</details>

#### baremetal allowed families contains common

- baremetal allowed families contains common
- baremetal allowed families contains common
   - Expected: families[1] equals `common`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("baremetal allowed families contains common")
step("baremetal allowed families contains common")
val families = baremetal_allowed_families()
expect(families[1]).to_equal("common")
```

</details>

#### baremetal blocks gc_async_mut

- baremetal blocks gc_async_mut
- baremetal blocks gc_async_mut
   - Expected: is_family_allowed(families, "gc_async_mut") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("baremetal blocks gc_async_mut")
step("baremetal blocks gc_async_mut")
val families = baremetal_allowed_families()
expect(is_family_allowed(families, "gc_async_mut")).to_equal(false)
```

</details>

#### baremetal blocks nogc_sync_mut

- baremetal blocks nogc_sync_mut
- baremetal blocks nogc_sync_mut
   - Expected: is_family_allowed(families, "nogc_sync_mut") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("baremetal blocks nogc_sync_mut")
step("baremetal blocks nogc_sync_mut")
val families = baremetal_allowed_families()
expect(is_family_allowed(families, "nogc_sync_mut")).to_equal(false)
```

</details>

#### baremetal allows nogc_async_mut_noalloc

- baremetal allows nogc_async_mut_noalloc
- baremetal allows nogc_async_mut_noalloc
   - Expected: is_family_allowed(families, "nogc_async_mut_noalloc") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("baremetal allows nogc_async_mut_noalloc")
step("baremetal allows nogc_async_mut_noalloc")
val families = baremetal_allowed_families()
expect(is_family_allowed(families, "nogc_async_mut_noalloc")).to_equal(true)
```

</details>

#### baremetal allows common

- baremetal allows common
- baremetal allows common
   - Expected: is_family_allowed(families, "common") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("baremetal allows common")
step("baremetal allows common")
val families = baremetal_allowed_families()
expect(is_family_allowed(families, "common")).to_equal(true)
```

</details>

#### target preset — hosted

#### hosted allowed families is empty (no restriction)

- hosted allowed families is empty (no restriction)
- hosted allowed families is empty (no restriction)
   - Expected: families.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("hosted allowed families is empty (no restriction)")
step("hosted allowed families is empty (no restriction)")
val families = hosted_allowed_families()
expect(families.len()).to_equal(0)
```

</details>

#### hosted allows gc_async_mut (empty list = no restriction)

- hosted allows gc_async_mut (empty list = no restriction)
- hosted allows gc_async_mut (empty list = no restriction)
   - Expected: is_family_allowed(families, "gc_async_mut") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("hosted allows gc_async_mut (empty list = no restriction)")
step("hosted allows gc_async_mut (empty list = no restriction)")
val families = hosted_allowed_families()
expect(is_family_allowed(families, "gc_async_mut")).to_equal(true)
```

</details>

#### hosted allows nogc_sync_mut

- hosted allows nogc_sync_mut
- hosted allows nogc_sync_mut
   - Expected: is_family_allowed(families, "nogc_sync_mut") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("hosted allows nogc_sync_mut")
step("hosted allows nogc_sync_mut")
val families = hosted_allowed_families()
expect(is_family_allowed(families, "nogc_sync_mut")).to_equal(true)
```

</details>

#### hosted allows nogc_async_mut_noalloc

- hosted allows nogc_async_mut_noalloc
- hosted allows nogc_async_mut_noalloc
   - Expected: is_family_allowed(families, "nogc_async_mut_noalloc") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("hosted allows nogc_async_mut_noalloc")
step("hosted allows nogc_async_mut_noalloc")
val families = hosted_allowed_families()
expect(is_family_allowed(families, "nogc_async_mut_noalloc")).to_equal(true)
```

</details>

#### target preset — embedded_with_heap

#### embedded_with_heap allowed families has exactly four entries

- embedded_with_heap allowed families has exactly four entries
- embedded_with_heap allowed families has exactly four entries
   - Expected: families.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("embedded_with_heap allowed families has exactly four entries")
step("embedded_with_heap allowed families has exactly four entries")
val families = embedded_with_heap_allowed_families()
expect(families.len()).to_equal(4)
```

</details>

#### embedded_with_heap contains nogc_async_mut_noalloc

- embedded_with_heap contains nogc_async_mut_noalloc
- embedded_with_heap contains nogc_async_mut_noalloc
   - Expected: families[0] equals `nogc_async_mut_noalloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("embedded_with_heap contains nogc_async_mut_noalloc")
step("embedded_with_heap contains nogc_async_mut_noalloc")
val families = embedded_with_heap_allowed_families()
expect(families[0]).to_equal("nogc_async_mut_noalloc")
```

</details>

#### embedded_with_heap contains nogc_sync_mut

- embedded_with_heap contains nogc_sync_mut
- embedded_with_heap contains nogc_sync_mut
   - Expected: families[1] equals `nogc_sync_mut`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("embedded_with_heap contains nogc_sync_mut")
step("embedded_with_heap contains nogc_sync_mut")
val families = embedded_with_heap_allowed_families()
expect(families[1]).to_equal("nogc_sync_mut")
```

</details>

#### embedded_with_heap contains nogc_async_mut

- embedded_with_heap contains nogc_async_mut
- embedded_with_heap contains nogc_async_mut
   - Expected: families[2] equals `nogc_async_mut`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("embedded_with_heap contains nogc_async_mut")
step("embedded_with_heap contains nogc_async_mut")
val families = embedded_with_heap_allowed_families()
expect(families[2]).to_equal("nogc_async_mut")
```

</details>

#### embedded_with_heap contains common

- embedded_with_heap contains common
- embedded_with_heap contains common
   - Expected: families[3] equals `common`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("embedded_with_heap contains common")
step("embedded_with_heap contains common")
val families = embedded_with_heap_allowed_families()
expect(families[3]).to_equal("common")
```

</details>

#### embedded_with_heap blocks gc_async_mut

- embedded_with_heap blocks gc_async_mut
- embedded_with_heap blocks gc_async_mut
   - Expected: is_family_allowed(families, "gc_async_mut") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("embedded_with_heap blocks gc_async_mut")
step("embedded_with_heap blocks gc_async_mut")
val families = embedded_with_heap_allowed_families()
expect(is_family_allowed(families, "gc_async_mut")).to_equal(false)
```

</details>

#### is_family_allowed helper

#### returns true when restriction list is empty

- returns true when restriction list is empty
- returns true when restriction list is empty
   - Expected: is_family_allowed(families, "gc_async_mut") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns true when restriction list is empty")
step("returns true when restriction list is empty")
val families: [text] = []
expect(is_family_allowed(families, "gc_async_mut")).to_equal(true)
```

</details>

#### returns true for any family when list is empty

- returns true for any family when list is empty
- returns true for any family when list is empty
   - Expected: is_family_allowed(families, "nogc_sync_mut") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns true for any family when list is empty")
step("returns true for any family when list is empty")
val families: [text] = []
expect(is_family_allowed(families, "nogc_sync_mut")).to_equal(true)
```

</details>

#### returns true for listed family

- returns true for listed family
- returns true for listed family
   - Expected: is_family_allowed(families, "nogc_async_mut_noalloc") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns true for listed family")
step("returns true for listed family")
val families = ["nogc_async_mut_noalloc", "common"]
expect(is_family_allowed(families, "nogc_async_mut_noalloc")).to_equal(true)
```

</details>

#### returns false for non-listed family

- returns false for non-listed family
- returns false for non-listed family
   - Expected: is_family_allowed(families, "gc_async_mut") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns false for non-listed family")
step("returns false for non-listed family")
val families = ["nogc_async_mut_noalloc", "common"]
expect(is_family_allowed(families, "gc_async_mut")).to_equal(false)
```

</details>

#### returns false for another non-listed family

- returns false for another non-listed family
- returns false for another non-listed family
   - Expected: is_family_allowed(families, "nogc_sync_mut") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns false for another non-listed family")
step("returns false for another non-listed family")
val families = ["nogc_async_mut_noalloc", "common"]
expect(is_family_allowed(families, "nogc_sync_mut")).to_equal(false)
```

</details>

#### gc_mode_from_family_prefix

#### nogc_sync_mut prefix maps to nogc mode

- nogc_sync_mut prefix maps to nogc mode
- nogc_sync_mut prefix maps to nogc mode
   - Expected: local_gc_mode_from_prefix("nogc_sync_mut.fs") equals `nogc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("nogc_sync_mut prefix maps to nogc mode")
step("nogc_sync_mut prefix maps to nogc mode")
expect(local_gc_mode_from_prefix("nogc_sync_mut.fs")).to_equal("nogc")
```

</details>

#### nogc_async_mut prefix maps to nogc mode

- nogc_async_mut prefix maps to nogc mode
- nogc_async_mut prefix maps to nogc mode
   - Expected: local_gc_mode_from_prefix("nogc_async_mut.thread") equals `nogc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("nogc_async_mut prefix maps to nogc mode")
step("nogc_async_mut prefix maps to nogc mode")
expect(local_gc_mode_from_prefix("nogc_async_mut.thread")).to_equal("nogc")
```

</details>

#### nogc_async_mut_noalloc prefix maps to nogc mode

- nogc_async_mut_noalloc prefix maps to nogc mode
- nogc_async_mut_noalloc prefix maps to nogc mode
   - Expected: local_gc_mode_from_prefix("nogc_async_mut_noalloc.exec") equals `nogc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("nogc_async_mut_noalloc prefix maps to nogc mode")
step("nogc_async_mut_noalloc prefix maps to nogc mode")
expect(local_gc_mode_from_prefix("nogc_async_mut_noalloc.exec")).to_equal("nogc")
```

</details>

#### gc_async_mut prefix maps to gc mode

- gc_async_mut prefix maps to gc mode
- gc_async_mut prefix maps to gc mode
   - Expected: local_gc_mode_from_prefix("gc_async_mut.alloc") equals `gc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gc_async_mut prefix maps to gc mode")
step("gc_async_mut prefix maps to gc mode")
expect(local_gc_mode_from_prefix("gc_async_mut.alloc")).to_equal("gc")
```

</details>

#### common prefix maps to gc mode

- common prefix maps to gc mode
- common prefix maps to gc mode
   - Expected: local_gc_mode_from_prefix("common.text") equals `gc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("common prefix maps to gc mode")
step("common prefix maps to gc mode")
expect(local_gc_mode_from_prefix("common.text")).to_equal("gc")
```

</details>

#### std. prefixed nogc path maps to nogc mode

- std. prefixed nogc path maps to nogc mode
- std. prefixed nogc path maps to nogc mode
   - Expected: local_gc_mode_from_prefix("std.nogc_sync_mut.fs") equals `nogc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("std. prefixed nogc path maps to nogc mode")
step("std. prefixed nogc path maps to nogc mode")
expect(local_gc_mode_from_prefix("std.nogc_sync_mut.fs")).to_equal("nogc")
```

</details>

#### unknown prefix maps to unknown

- unknown prefix maps to unknown
- unknown prefix maps to unknown
   - Expected: local_gc_mode_from_prefix("mylib.foo") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("unknown prefix maps to unknown")
step("unknown prefix maps to unknown")
expect(local_gc_mode_from_prefix("mylib.foo")).to_equal("unknown")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-RUNTIMEFAMILY-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `74ea7500f337001261e7cf10350793e59c018aca20fd6b8dd29cae20e2dd3a31`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `74ea7500f337001261e7cf10350793e59c018aca20fd6b8dd29cae20e2dd3a31`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `74ea7500f337001261e7cf10350793e59c018aca20fd6b8dd29cae20e2dd3a31`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/runtime_family_spec.spl
mirror: doc/06_spec/integration/runtime_family_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/runtime_family_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/runtime_family_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/runtime_family_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/runtime_family_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'baremetal allowed families has exactly two entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/runtime_family_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'baremetal allowed families contains nogc_async_mut_noalloc' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/runtime_family_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'baremetal allowed families contains common' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
