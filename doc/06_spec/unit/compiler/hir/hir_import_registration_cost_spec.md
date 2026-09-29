# Hir Import Registration Cost Specification

> Tests covering HIR import registration resolution facts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Import Registration Cost Specification

## Scenarios

### HIR import registration resolution facts

#### resolves a qualified type name once per (surface, name), not once per importer

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### does not repeat a MISS -- the negative result is cached too

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = import_registry()
var lowering = hirlowering_for_module("pkg/imp1.spl", registry)
val span = Span.empty()
val decl = registry.surfaces[0]
# `pkg.decl` has no imports at all, so every query is a miss. A miss is
# exactly the case that used to re-sweep for every importer.
lowering.materialize_imported_callable_explicit_dependency(
    decl, "NeverDeclared", span, false)
lowering.materialize_imported_callable_explicit_dependency(
    decl, "NeverDeclared", span, false)
expect(lowering.explicit_dep_scan_count).to_equal(1)
expect(lowering.explicit_dep_target_memo["pkg.decl NeverDeclared"]).to_equal(-1)
```

</details>

#### still resolves a different dependency name, and a different surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = import_registry()
var lowering = hirlowering_for_module("pkg/imp1.spl", registry)
val span = Span.empty()
lowering.materialize_imported_callable_explicit_dependency(
    registry.surfaces[0], "One", span, false)
lowering.materialize_imported_callable_explicit_dependency(
    registry.surfaces[0], "Two", span, false)
lowering.materialize_imported_callable_explicit_dependency(
    registry.surfaces[1], "One", span, false)
expect(lowering.explicit_dep_scan_count).to_equal(3)
```

</details>

#### caches only SymbolId-free facts

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The whole safety argument: the cached value is a registry INDEX plus
# an item NAME, both stable for the frozen phase. SymbolIds are
# allocated per module and restart at 0 on `symbols.reset_module()`, so
# caching one across importers would hand a later module ids belonging
# to a different table -- the reason the two memos proposed in the bug
# record were rejected. `begin_module` must therefore leave this cache
# alone while still wiping the symbol table.
val registry = import_registry()
var lowering = hirlowering_for_module("pkg/imp1.spl", registry)
val span = Span.empty()
lowering.materialize_imported_callable_explicit_dependency(
    registry.surfaces[0], "Widget", span, false)
expect(lowering.explicit_dep_target_memo.len()).to_equal(1)
expect(lowering.explicit_dep_item_memo["pkg.decl Widget"]).to_equal("")
lowering.begin_module("pkg/imp2.spl")
expect(lowering.explicit_dep_target_memo.len()).to_equal(1)
```

</details>

#### leaves the lowered result unchanged: no symbol is defined for an unresolvable name

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Correctness half. The cache changes only how the answer is FOUND;
# every importer still runs its own registration against its own table.
# With no explicit import to follow, no importer gains a symbol and no
# diagnostic is raised -- identical to the pre-cache behaviour.
val registry = import_registry()
var lowering = hirlowering_for_module("pkg/imp1.spl", registry)
val span = Span.empty()
lowering.materialize_imported_callable_explicit_dependency(
    registry.surfaces[0], "NeverDeclared", span, false)
expect(lowering.errors.len()).to_equal(0)
lowering.begin_module("pkg/imp2.spl")
lowering.materialize_imported_callable_explicit_dependency(
    registry.surfaces[0], "NeverDeclared", span, false)
expect(lowering.errors.len()).to_equal(0)
expect(lowering.symbols.lookup_or_invalid("pkg.decl::NeverDeclared").is_valid()).to_equal(false)
```

</details>

#### keeps SymbolTable.define free of a second owner of the scope dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ALIAS1 (2026-08-21). Measured with a 15-line probe: 8000 successive
# `define` calls cost 1818 ms for the first 1000 and 8335 ms for the
# eighth, i.e. per-call cost linear in the table already built -- the
# same growth law the real closure shows for `register_imported_symbol`
# (1.7 -> 15.8 ms/call). SIMPLE_PERF_COUNTERS=1 reports
# VT_OBJECT_FIELD_CLONES=8000, exactly one value-type object copy per
# define: the scope row is read out by value and written back, so its
# `symbols` Dict is cloned on every write.
#
# `define` used to hold TWO extra owners of that dict: a `scope_syms`
# local and a `self.root_scope_symbols` mirror. The mirror was dead --
# it is only ever read immediately after being reassigned, in
# `reset_module` and `new` -- and each extra owner forces another
# copy-on-write. Dropping both took the probe from 33.7 s to 27.6 s and
# the first block from 1818 ms to 904 ms.
#
# A source-shape contract rather than a clone counter because the
# counters live in the Rust seed and are not reachable from Simple.
#
# SCOPEIP (2026-08-21): the LAST owner is gone too. The `var scope`
# round trip survived only because `self.scopes[i].symbols[name] = v`
# used to be rejected with "semantic: invalid assignment: complex field
# access not supported"; nested assignment targets are supported now
# (344f277cc45), so the scope row is written in place and `define` no
# longer reads a value-type row out and writes it back.
val source = file_read("src/compiler/20.hir/hir_types.spl")
val start = source.index_of("me define(name: text, kind: SymbolKind")
expect(start).to_be_greater_than(0)
val body = source.substring(start, source.index_of(
    "me bind_qualified_function(", start))
expect(body.contains("var scope_syms = scope.symbols")).to_equal(false)
expect(body.contains("self.root_scope_symbols = scope_syms")).to_equal(false)
expect(body.contains("var scope = self.scopes[self.current_scope.id]")).to_equal(false)
expect(body.contains("self.scopes[self.current_scope.id] = scope")).to_equal(false)
expect(body).to_contain("self.scopes[self.current_scope.id].symbols[name] = raw_id")
```

</details>

#### registers one (surface, name, local, enum) tuple once per importer

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RISDONE (2026-08-21). `register_imported_symbol` is idempotent within
# one importer -- every branch re-checks `already_bound` before it
# writes -- but a repeat still re-ran six surface name scans and
# re-descended the whole field / method / payload subtree under it.
# driver.spl issued 8,284 registrations for a far smaller distinct set,
# and 377 s of its 427 s HIR was inside the field-dependency descent.
# Counter, not wall clock: it cannot pass on the pre-fix code.
val registry = import_registry()
var lowering = hirlowering_for_module("pkg/imp1.spl", registry)
val span = Span.empty()
val decl = registry.surfaces[0]
lowering.register_imported_symbol(decl, "pkg.decl", "Widget", "Widget", span, false)
expect(lowering.registered_import_skip_count).to_equal(0)
lowering.register_imported_symbol(decl, "pkg.decl", "Widget", "Widget", span, false)
lowering.register_imported_symbol(decl, "pkg.decl", "Widget", "Widget", span, false)
expect(lowering.registered_import_skip_count).to_equal(2)
# A different local name, a different imported name, and a different
# materialize_enum flag are all DIFFERENT registrations: each writes a
# different binding, so none of them may be skipped.
lowering.register_imported_symbol(decl, "pkg.decl", "Widget", "pkg.decl::Widget", span, false)
lowering.register_imported_symbol(decl, "pkg.decl", "Other", "Other", span, false)
lowering.register_imported_symbol(decl, "pkg.decl", "Widget", "Widget", span, true)
expect(lowering.registered_import_skip_count).to_equal(2)
```

</details>

#### never carries a completed registration across importers

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The safety argument. Unlike `explicit_dep_target_memo` (a pure
# function of the frozen registry) this memo records work done against
# ONE importer's symbol table, which `begin_module` wipes. Carrying it
# over would leave the next importer with no binding at all.
val registry = import_registry()
var lowering = hirlowering_for_module("pkg/imp1.spl", registry)
val span = Span.empty()
val decl = registry.surfaces[0]
lowering.register_imported_symbol(decl, "pkg.decl", "Widget", "Widget", span, false)
lowering.begin_module("pkg/imp2.spl")
expect(lowering.registered_import_memo.len()).to_equal(0)
lowering.register_imported_symbol(decl, "pkg.decl", "Widget", "Widget", span, false)
expect(lowering.registered_import_skip_count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/hir/hir_import_registration_cost_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HIR import registration resolution facts.
- HIR import registration resolution facts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `e60a0d61e4abf2735607eb7acb84354b3f2534c8ea1423980bf72bd3b5e7a6af`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e60a0d61e4abf2735607eb7acb84354b3f2534c8ea1423980bf72bd3b5e7a6af`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e60a0d61e4abf2735607eb7acb84354b3f2534c8ea1423980bf72bd3b5e7a6af`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/unit/compiler/hir/hir_import_registration_cost_spec.spl
mirror: doc/06_spec/unit/compiler/hir/hir_import_registration_cost_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/hir/hir_import_registration_cost_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/hir/hir_import_registration_cost_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/hir/hir_import_registration_cost_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/unit/compiler/hir/hir_import_registration_cost_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/hir/hir_import_registration_cost_spec.spl:54:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'resolves a qualified type name once per (surface, name), not once per importer' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/compiler/hir/hir_import_registration_cost_spec.spl:78:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'does not repeat a MISS -- the negative result is cached too' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/compiler/hir/hir_import_registration_cost_spec.spl:93:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'still resolves a different dependency name, and a different surface' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/compiler/hir/hir_import_registration_cost_spec.spl:106:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'caches only SymbolId-free facts' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
