# hir_glob_reachable_miss_memo_spec

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hir_glob_reachable_miss_memo_spec

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_glob_reachable_miss_memo_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/hir/hir_glob_reachable_miss_memo_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### HIR glob-reachable resolution facts

#### sweeps once per (importer, unbound name), not once per occurrence

- Verify: sweeps once per (importer, unbound name), not once per occurrence
   - Expected: lowering.glob_reachable_scan_count equals `1`
   - Expected: lowering.glob_reachable_scan_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: sweeps once per (importer, unbound name), not once per occurrence")
val registry = glob_registry()
var lowering = hirlowering_for_module("pkg/imp1.spl", registry)
val span = Span.empty()
# The same unbound name asked three times, exactly as a module body
# naming one unresolvable type three times would ask it.
expect(lowering.try_register_glob_reachable_symbol("NeverDeclared", span)).to_be(false)
expect(lowering.glob_reachable_scan_count).to_equal(1)
expect(lowering.try_register_glob_reachable_symbol("NeverDeclared", span)).to_be(false)
expect(lowering.try_register_glob_reachable_symbol("NeverDeclared", span)).to_be(false)
expect(lowering.glob_reachable_scan_count).to_equal(1)
```

</details>

#### still sweeps for a DIFFERENT name -- the memo is per name, not a latch

- Verify: still sweeps for a DIFFERENT name -- the memo is per name, not a latch
   - Expected: lowering.glob_reachable_scan_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: still sweeps for a DIFFERENT name -- the memo is per name, not a latch")
val registry = glob_registry()
var lowering = hirlowering_for_module("pkg/imp1.spl", registry)
val span = Span.empty()
expect(lowering.try_register_glob_reachable_symbol("One", span)).to_be(false)
expect(lowering.try_register_glob_reachable_symbol("Two", span)).to_be(false)
expect(lowering.glob_reachable_scan_count).to_equal(2)
```

</details>

#### still sweeps for a DIFFERENT importer -- the memo is not shared across modules

- Verify: still sweeps for a DIFFERENT importer -- the memo is not shared across modules
   - Expected: lowering.glob_reachable_scan_count equals `1`
   - Expected: lowering.glob_reachable_scan_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: still sweeps for a DIFFERENT importer -- the memo is not shared across modules")
# The sweep's one importer-local step (`register_imported_symbol`)
# writes into the IMPORTING module's symbol table, so unlike the
# registry-pure `explicit_dep_target_memo` this answer must NOT be
# reused across importers. The key carries the importer surface index
# for exactly that reason.
val registry = glob_registry()
var lowering = hirlowering_for_module("pkg/imp1.spl", registry)
val span = Span.empty()
expect(lowering.try_register_glob_reachable_symbol("Shared", span)).to_be(false)
expect(lowering.glob_reachable_scan_count).to_equal(1)
lowering.begin_module("pkg/imp2.spl")
expect(lowering.try_register_glob_reachable_symbol("Shared", span)).to_be(false)
expect(lowering.glob_reachable_scan_count).to_equal(2)
```

</details>

#### answers the declaration question identically to the linear predicate

- Verify: answers the declaration question identically to the linear predicate


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: answers the declaration question identically to the linear predicate")
# The other half of the fix routes `hir_module_declares_item`'s six
# linear name-array sweeps through the existing NAMEIDX per-surface
# index. Same predicate, so the two must agree -- on a name that is
# declared and on one that is not.
val registry = glob_registry()
var lowering = hirlowering_for_module("pkg/imp1.spl", registry)
val decl = registry.surfaces[0]
expect(lowering.surface_declares_item_indexed(decl, "Absent"))
    .to_equal(hir_module_declares_item(decl, "Absent"))
expect(lowering.surface_declares_item_indexed(decl, "AlsoAbsent"))
    .to_equal(hir_module_declares_item(decl, "AlsoAbsent"))
```

</details>

#### leaves the lowered result unchanged: a memoized miss still defines no symbol

- Verify: leaves the lowered result unchanged: a memoized miss still defines no symbol
   - Expected: lowering.symbols.lookup_or_invalid("NeverDeclared").id equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: leaves the lowered result unchanged: a memoized miss still defines no symbol")
# Correctness half. The memo changes only how often the answer is
# recomputed, never what it is: an unresolvable name stays unresolved
# and no symbol is invented for it.
val registry = glob_registry()
var lowering = hirlowering_for_module("pkg/imp1.spl", registry)
val span = Span.empty()
lowering.try_register_glob_reachable_symbol("NeverDeclared", span)
lowering.try_register_glob_reachable_symbol("NeverDeclared", span)
expect(lowering.symbols.lookup_or_invalid("NeverDeclared").id).to_equal(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3e46c386959d51e8b062d2cfb74a5cd2270b8c87c28cb0c9fd4e90519bb2c2f9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3e46c386959d51e8b062d2cfb74a5cd2270b8c87c28cb0c9fd4e90519bb2c2f9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3e46c386959d51e8b062d2cfb74a5cd2270b8c87c28cb0c9fd4e90519bb2c2f9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/hir/hir_glob_reachable_miss_memo_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_glob_reachable_miss_memo_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/hir_glob_reachable_miss_memo_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_glob_reachable_miss_memo_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_glob_reachable_miss_memo_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/hir_glob_reachable_miss_memo_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sweeps once per (importer, unbound name), not once per occurrence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_glob_reachable_miss_memo_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still sweeps for a DIFFERENT name -- the memo is per name, not a latch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_glob_reachable_miss_memo_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still sweeps for a DIFFERENT importer -- the memo is not shared across modules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/compiler/hir/hir_glob_reachable_miss_memo_spec.spl. -->
