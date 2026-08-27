# Gc Family Boundary Hook Specification

> Tests covering interpreter gc family boundary hook wiring.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Family Boundary Hook Specification

## Scenarios

### interpreter gc family boundary hook wiring

#### extracts noalloc before async mutable families

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts noalloc before async mutable families


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts noalloc before async mutable families")
val source = _source()
val noalloc_pos = source.index_of("contains(\"/nogc_async_mut_noalloc/\")")
val async_pos = source.index_of("contains(\"/nogc_async_mut/\")")
expect(noalloc_pos).to_be_greater_than(-1)
expect(async_pos).to_be_greater_than(-1)
expect(noalloc_pos).to_be_less_than(async_pos)
```

</details>

#### skips unknown and common families before warning

- skips unknown and common families before warning


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips unknown and common families before warning")
val source = _source()
expect(source).to_contain("if importer_family == \"\" or imported_family == \"\":")
expect(source).to_contain("if importer_family == \"common\" or imported_family == \"common\":")
```

</details>

#### warns for no-gc importing gc

- warns for no-gc importing gc


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns for no-gc importing gc")
val source = _source()
expect(source).to_contain("if is_nogc_family(importer_family) and is_gc_family(imported_family):")
expect(source).to_contain("GC module")
expect(source).to_contain("eval_warnings.push(msg)")
expect(source).to_contain("print msg")
```

</details>

#### warns for noalloc importing allocating family

- warns for noalloc importing allocating family


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns for noalloc importing allocating family")
val source = _source()
expect(source).to_contain("if is_noalloc_family(importer_family) and is_allocating_family(imported_family):")
expect(source).to_contain("Allocating module")
expect(source).to_contain("print msg")
```

</details>

#### deduplicates warning keys

- deduplicates warning keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deduplicates warning keys")
val source = _source()
expect(source).to_contain("val warn_key = importer_family + \">\" + imported_family + \":\" + module_name")
expect(source).to_contain("_gc_warn_emitted.has(warn_key)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/gc_family_boundary_hook_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering interpreter gc family boundary hook wiring.
- interpreter gc family boundary hook wiring

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `06672373a11edcdd00de476037005692dde74de2eb72249145a761f57afa2bbd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `06672373a11edcdd00de476037005692dde74de2eb72249145a761f57afa2bbd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `06672373a11edcdd00de476037005692dde74de2eb72249145a761f57afa2bbd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interpreter/gc_family_boundary_hook_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/gc_family_boundary_hook_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/gc_family_boundary_hook_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/gc_family_boundary_hook_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/gc_family_boundary_hook_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts noalloc before async mutable families' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/gc_family_boundary_hook_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips unknown and common families before warning' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/gc_family_boundary_hook_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns for no-gc importing gc' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
