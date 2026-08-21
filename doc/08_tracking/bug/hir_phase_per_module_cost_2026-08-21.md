# HIR phase costs ~20x parse per module (full-registry rescans) — 2026-08-21

## Status
RESOLVED 2026-08-21 — a865dced154 memoizes frozen-registry owner scans in the package-dep and bootstrap-global resolvers. Evidence: per-module HIR lowering 0.28s -> 0.15s (61-module fixture), per commit message and hir_package_dependency_scan_memo_spec.spl.


## Symptom
Stage1 bootstrap (self-hosted `src/compiler` interpreted by the Rust seed):
parse finished 662 modules in ~50 min (~5 s/module); the HIR phase
(`[build] hir N/662`, step 2/6) managed 33 modules in ~55 min (~100 s/module)
in run1 — HIR alone extrapolates to ~18 h.

## Mechanism (defect, not inherent cost)
Two HIR resolvers scan the ENTIRE frozen module-surface registry (662 surfaces)
with no early exit — they must prove the owner is UNIQUE — and both are invoked
per consumer rather than per answer. The registry is frozen for the whole HIR
phase, so every one of those scans recomputes a constant.

1. `_Items/module_reexport_materialization.spl`
   `materialize_imported_field_package_dependency`: full `surfaces` sweep per
   unresolved composite-FIELD dependency, calling `module_surface_package_name`
   (canonicalize + `split(".")` + slice + `join(".")`, i.e. a heap allocation)
   and `hir_module_declares_item` (6 dict probes) per candidate.
   Cost: O(modules x registry x field-deps) with per-candidate allocation.
2. `_Items/module_import_registration.spl`
   `try_register_bootstrap_global_symbol`: same full sweep, but invoked LAZILY
   from BODY lowering for every UNBOUND NAME (see the BGS1 note there).
   Cost: O(bodies x names x registry).

Neither depends on the module's own size, which is why HIR — not parse — is the
phase that blows up as the closure grows.

## Fix
Memoize both, since the registry is immutable for the phase:
- `field_package_dep_memo` keyed by (declaring module, dependency) -> surface
  index, `-1` for none/ambiguous (both were already no-ops).
- `bootstrap_global_owner_memo` keyed by name -> owning surface index.
- `surface_package_name_memo` (per surface module name) removes the split/join
  allocation from the inner loop.
Two observable scan counters (`field_package_dep_scan_count`,
`bootstrap_global_scan_count`) make the mechanism testable rather than only
timeable. Semantics unchanged: the ambiguity early-return is preserved as a
memoized `-1`.

## Measurement
Fixture: 61-module single-package closure whose composites carry field types
declared by a package SIBLING with no import edge (exactly the shape that drives
resolver 1), built with the same seed and driver as the bootstrap, `--threads 1`.
Wall time of the `[build] hir` span, from per-line timestamps:

| | HIR span (61 modules) | per module |
|---|---|---|
| pre  | 17 s | 0.28 s |
| post |  9 s | 0.15 s |

1.9x on a 61-surface registry. The eliminated term is linear in registry size,
so the bootstrap's 662-surface registry is ~11x further from the memo-hit path
than this fixture. Diagnostics are byte-identical pre/post (same 123,681-byte
stderr, only the pid in the temp-file name differs), so no error changed.

## Pin
`test/01_unit/compiler/hir/hir_package_dependency_scan_memo_spec.spl` asserts
the scan COUNT, not a wall clock: repeated identical queries scan once, a
different dependency name scans again, and a surface's package name is computed
once. It pins the algorithm, so it cannot pass on the pre-fix code (the counters
did not exist) and cannot be satisfied by a faster machine.

## Follow-up landed the same day: inverted indices (2026-08-21, second commit)
The memos above still answered each question with a full-registry sweep the
FIRST time, and a third resolver had no memo at all. All three now read an index
built once per lowerer from the frozen registry:

- `surface_decl_owners` (`{name: [surface_index]}`, built in
  `_Items/module_lowering.spl`) replaces the sweeps in
  `try_register_bootstrap_global_symbol` (a non-singleton owner list is exactly
  the old "ambiguous -> give up") and in
  `materialize_imported_field_package_dependency`, whose candidate loop now runs
  over the one or two surfaces that declare the name at all. The
  `bootstrap_global_owner_memo` added by the first commit is therefore gone —
  the index subsumes it.
- `package_sibling_names` / `package_sibling_canons` (canonical package ->
  member modules) replace the per-module sweep over every registry KEY in
  `resolve_package_sibling_symbols`
  (`_Items/module_import_resolution.spl`), which canonicalized each key with a
  split/join and deduplicated into a fresh dict on every module lowered. The
  dedup by canonical name now happens once, during the index build.

Measured on a 240-module package fixture of the same shape, `--threads 1`,
`[build] hir` span:

| | HIR span (240 modules) | per module |
|---|---|---|
| memos only (a865dced154) | 54 s | 0.225 s |
| + inverted indices | **32 s** | **0.133 s** |

Per-module cost is now flat between the 61- and 240-module fixtures (0.15 s vs
0.13 s), which is the property that was missing: the eliminated terms were all
linear in registry size, so they grew with the closure rather than with the
module. Diagnostics are unchanged (same stderr content on the 61-module fixture;
only blank-line wrapping of the truncation banner differs).

Pin: two further examples in the same spec assert that the declaration-owner
index and the package-sibling index are each built exactly ONCE no matter how
many distinct names or packages are queried.

## Third commit: registry KEY lookup was also linear
`hir_module_surface_index` (`_Items/module_lowering.spl:131`) compared every
registry key in `ordered_names` (~2 per module, ~1300 in a full bootstrap) to
resolve ONE name, and is called per import, per package sibling and per
re-export hop. Replaced at the five in-lowerer call sites by
`surface_index_for_name`, a dict probe over an index built once from the same
aligned arrays (values are i64, so the ModuleSurface-payload hazard documented
on the linear form does not apply). First-alias-wins and the out-of-range
bounds check are preserved exactly.

240-module fixture, `[build] hir` span: 32 s -> **27 s** (0.133 -> 0.113 s per
module). Cumulative for the day on that fixture: 54 s -> 27 s, 2.0x, with the
per-module cost now flat in registry size. Diagnostics unchanged.

## Not fixed here
`hir_module_declares_item` is still a linear probe of six dicts when called
directly (the index calls it implicitly, once per surface, at build time), and
the surface registry itself is still rebuilt per lowerer rather than shared
across phases. Neither is multiplicative any more.

## Real-closure follow-up (2026-08-21, later session)

The registry memos/indexes above were measured on FIXTURE packages (61 and 240
modules, 0.11 s/module). The real 662-module stage1 closure still cost
60-190 s/module, so a mechanism was scaling with the closure that fixtures do
not exercise. Two things were established, one fixed and one measured.

### Fixed: `field_module_callable` swept the whole symbol table

`HirLowering.field_module_callable`
(`src/compiler/20.hir/hir_lowering/_Expressions/expression_support.spl:171`)
materialized `self.symbols.symbols.keys()` -- an array over the ENTIRE symbol
table -- and scanned it in reverse. Its only gate is "the receiver symbol has
a `defining_module`", which is true for every imported symbol, so it ran on
essentially every `x.field` / `x.method(...)` in every body. Fixture symbol
tables hold tens of symbols; the real closure holds tens of thousands.

Replaced by `SymbolTable.module_callables`, a `{defining_module}#{name}` index
(also keyed by the name's last dotted segment, matching the sweep's
`ends_with("." + field)` arm) maintained in `define()`,
`register_preserved_symbol()`, `rename_symbol()`, and cleared by
`reset_module()`. Commit `45749fb5130`; mechanism spec
`test/01_unit/compiler/hir/hir_module_callable_index_spec.spl` (6/6).

Real-closure effect, same lane and box, `[build] hir` `dt=` stamps:

| module | before | after |
|---|---|---|
| `compiler.common.driver_core_types` | 354238 ms | 191286 ms |
| `compiler.common.driver_core_types` (alias pass) | 11322 ms | 6143 ms |
| `compiler.driver.driver_riscv_gen2_product` | 136600 ms | 135867 ms |

So it is roughly a 45% cut on import-heavy modules and no change on others --
real, but not the whole story. (Different processes on a shared box; treat as
an envelope, not a controlled A/B.)

### Measured: the remaining cost is import REGISTRATION, not glob expansion

`SIMPLE_HIR_PHASE_PROFILE=1` (new, default off,
`src/compiler/20.hir/hir_lowering/hir_phase_profile.spl`) emits one row per
lowered module splitting its wall time into imports / declare / enums /
functions / other, with the glob walk timed separately inside imports and
`other` computed as the residual so nothing can hide in an uninstrumented gap.
Real closure, first modules of phase 2/6:

| module | total | imports | glob roots | expansions | reg_imported | enums | functions | other |
|---|---|---|---|---|---|---|---|---|
| `compiler/driver/driver.spl` | 161207 ms | **148777 ms (92%)** | 69223 ms / 6 | 73 | 9435 | 11265 ms (177) | 118 ms | 993 ms |
| `app/cli/bootstrap_main.spl` | 56371 ms | **42718 ms (76%)** | 0 ms / 0 | 3 | 2163 | 5558 ms (100) | 7965 ms | 6 ms |
| `common/driver_core_types.spl` | 5171 ms | 5136 ms (99%) | 0 ms / 0 | 14 | 792 | 34 ms (5) | 0 ms | 1 ms |
| `std/.../io/file_ops.spl` (cheap) | 3465 ms | 1340 ms (39%) | 0 ms / 0 | 8 | 563 | 0 ms | 1739 ms | 14 ms |
| `app/cli/bootstrap_identity.spl` (cheap) | 272 ms | 249 ms | 0 ms / 0 | 3 | 143 | 0 ms | 17 ms | 2 ms |

Body lowering is NOT the cost (118 ms of 161 s on `driver.spl`). The glob walk
is NOT the cost either: 73 expansions for 9435 registrations -- the GLB2 memo
is working exactly as its note claims.

The signal is the PER-CALL cost of `register_imported_symbol`, and it grows
with the accumulated closure: 1.7 ms/call (`bootstrap_identity`, 143 calls) ->
2.8 ms (`io_runtime`) -> 6.5 ms (`driver_core_types`, 792) -> **15.8 ms**
(`driver.spl`, 9435). A registration is nominally a dict probe plus a
`define()`. The next suspect is the work reached from it --
`materialize_imported_callable_type_dependencies`
(`_Items/module_reexport_materialization.spl:564`), which for every param and
return type of every imported callable does a qualified-type lookup and, on a
miss, a declared- then explicit-dependency materialization; the misses repeat
per importer.

### Two proposed fixes that are NOT safe, with the reason

Both were considered and rejected on code evidence, not preference:

1. **Making `glob_expand_memo` phase-lifetime** (i.e. not clearing it at
   `context_helpers.spl:83`) would be a correctness bug, not a speedup.
   The memo does not cache a RESULT; it guards re-entry within one root
   expansion, and the walk's side effect is `register_imported_symbol` ->
   `SymbolTable.define()` into the CURRENT module's table, which
   `begin_module` wipes via `symbols.reset_module()` (`hir_types.spl:253`).
   A memo that survived the module boundary would make the second importer of
   a surface skip registration entirely and see no symbols. Note also that the
   memo is already reset per ROOT (`module_import_resolution.spl:65,74`), so
   the per-module clear is redundant and cannot be the cost -- and the profile
   above confirms the walk is 73 expansions, not thousands.

2. **Caching lowered imported enums across importers** (memo keyed by owner
   surface + enum name) is unsafe for the same reason: a lowered `HirEnum`
   carries `SymbolId`s allocated in the lowering module's table, and
   `reset_module()` sets `next_symbol_id = 0`, so ids restart per module. A
   cached `HirEnum` would hand a later importer symbol ids belonging to a
   different table. Enum re-lowering is real cost (11.3 s of 161 s on
   `driver.spl`, 177 lowerings) but any fix must re-key the symbols, not reuse
   them.

## Fourth session (2026-08-21): the sub-step split, and the real growth law

### Sub-step instrumentation

`SIMPLE_HIR_PHASE_PROFILE=1` now emits a second line, `[hir-prof-ris]`, splitting
what `register_imported_symbol` reaches: `callable_deps` / `declared_dep` /
`explicit_dep` (with the number of `use`-item sweeps and items compared) /
`field_dep` / `payload` / `methods` / `sigtype` / `define` / `canon`, plus a
qualified-type `queries/misses` pair. The RIS slots are nested inside `imports`
and inside each other, so they are reported separately and never added to
`measured` -- `other` stays a true residual.

### The growth law is an ALIASING copy, not a miss

The previous section's suspicion (repeated qualified-type MISSES) is real but
secondary. The dominant term is that **`SymbolTable.define` copied the whole
scope symbol dict on every call**, so registration cost is linear in the table
already built and the phase is O(n^2) in a module's import count.

Reproduced in a 15-line probe (8000 successive `define` calls, one process, one
tree, one binary), block cost per 1000 defines:

| defines | pre | post |
|---|---|---|
| 1000 | 1818 ms | 904 ms |
| 4000 | 3792 ms | 3117 ms |
| 8000 | 8335 ms | 6358 ms |
| total | 33.7 s | 27.6 s |

`SIMPLE_PERF_COUNTERS=1` on the same probe: `VT_OBJECT_FIELD_CLONES = 8000`,
exactly one value-type object copy per define, with every array counter at 0.
That is `copy_value_type_in_place` on the scope row, whose `symbols` Dict field
is deep-copied with it.

**Why it happens.** Value semantics + copy-on-write means a write through a
collection with more than one owner clones it. `define`'s tail was

    var scope = self.scopes[self.current_scope.id]
    var scope_syms = scope.symbols          # owner 2
    scope_syms[name] = raw_id               # write while aliased -> full clone
    scope.symbols = scope_syms
    self.scopes[self.current_scope.id] = scope
    if self.current_scope.id == 0:
        self.root_scope_symbols = scope_syms  # owner 3, permanent

so scope 0 -- the scope every imported symbol lands in -- had a permanent second
owner and therefore cloned on *every* write. The `root_scope_symbols` mirror was
dead: it is only ever read immediately after being reassigned, in `new()` and
`reset_module()`. Both extra owners are removed. **Why fixtures never showed
it:** the cost is per-call linear in the table, and a 61- or 240-module fixture
builds tables of tens of symbols while `driver.spl` registers 9,435. **How to
spot the class:** per-call cost rising with an accumulated collection, plus a
non-zero clone counter that tracks call count 1:1.

What is NOT fixed: the remaining `var scope = ...` / write-back round trip still
copies once per define. It cannot be removed in Simple today --
`self.scopes[i].symbols[name] = v` is rejected with `semantic: invalid
assignment: complex field access not supported`. A seed-side change that lets
`Arc::make_mut` see a sole owner during self-update method calls is the general
fix and is tracked by a separate lane; the language gap is recorded here rather
than worked around.

### Also landed: phase-invariant import-resolution facts

`materialize_imported_callable_explicit_dependency` swept
`imported_mod.imports` x `import.items` for ONE dependency name, on every
qualified-type miss, per param, per callable, per IMPORTING module. The answer
depends only on the frozen registry and the DECLARING surface, so it is now
memoized on `(declaring module, dependency)` -> `(registry index, item name)`,
with `-1` for "no explicit import declares it" and `-2` for ambiguous. Negative
results are cached deliberately: a name that never resolves was the worst case,
re-swept by every importer. The ambiguity DIAGNOSTIC is still emitted per
importer, so no error changes.

Deliberately SymbolId-free: a registry index and an item name are stable for the
frozen phase, whereas SymbolIds restart at 0 on `symbols.reset_module()` -- the
exact reason the two memos proposed in the previous section were rejected. Every
importer still runs its own `register_imported_symbol` and `bind_qualified_type`
against its own table; only the RESOLUTION is shared.

Pin: `test/01_unit/compiler/hir/hir_import_registration_cost_spec.spl` (6/6,
plus mirror) asserts the sweep COUNT, that a miss is not repeated, that a
different name or surface still resolves, that `begin_module` leaves the cache
alone, and the alias-free shape of `define`.

### Not measured

The pre/post on the REAL 662-module closure. Two `native-build --entry-closure`
probes were run and both were killed in phase 1/6: the parse alone exceeded 25
minutes per attempt on this shared box, and the host hit 107/125 GB with three
lanes' shard workers resident, so the run could not be carried to
`compiler.driver.driver` in phase 2/6. The numbers above are therefore a
controlled single-tree A/B on the isolated mechanism, not a closure measurement.
Re-measuring driver.spl and bootstrap_main.spl HIR `dt=` remains open.
