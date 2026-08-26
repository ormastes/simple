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

## Fifth session (2026-08-21): where the 2.7x went, and the completed-registration memo

### The two real-closure profiles, same deployed seed

Both lines below come from the SAME binary
(`bin/release/x86_64-unknown-linux-gnu/simple`, built from `dee19c5bb80`), so
they compare TREES, not compilers. `[hir-prof]` is emitted by the seed, which is
why a tree that predates the profiler commit still produces the line.

| module | run6 tree `5020e8f3f45` | run7 tree `d1fd6255ecd` | ratio |
|---|---|---|---|
| `compiler/driver/driver.spl` total | 161,207 ms | 427,283 ms | 2.65x |
| … imports | 148,777 ms | 402,472 ms | 2.71x |
| … glob (6 roots, 73 expansions both) | 69,223 ms | 194,639 ms | 2.81x |
| … enums | 11,265 ms | 22,168 ms | 1.97x |
| … reg_imported | 9,435 | 8,284 | 0.88x |
| `app/cli/bootstrap_main.spl` total | 56,371 ms | 66,380 ms | 1.18x |
| `common/driver_core_types.spl` total | 5,171 ms | 7,049 ms | 1.36x |
| `cli/bootstrap_identity.spl` total | 272 ms | 220 ms | 0.81x |

Read that shape before blaming any one commit. The blow-up is **not uniform**:
small modules are flat or faster, and the one huge module got 2.7x worse while
performing FEWER registrations (9,435 -> 8,284). Whatever changed is superlinear
in the size of the import closure, not a constant factor added per call — which
is why the commit-by-commit bisect over the 19 commits in
`5020e8f3f45..d1fd6255ecd` was started but is not the fastest route to a fix: one
probe costs ~70 min wall (parse of the real closure alone is ~50 min at
`--threads 2`), so a 4-probe halving is ~5 h.

### What the RIS split actually names (run7, `driver.spl`)

    callable_deps 412,526 ms / 1,632    declared_dep 410,535 ms / 3,045
    field_dep     377,261 ms / 3,991    explicit_dep  19,599 ms / 5,764
    methods       146,273 ms /   784    define        15,297 ms / 1,529
    qtype 7,522 queries / 5,832 miss

These are INCLUSIVE and nested inside each other, so they do not sum to the
427 s total; the useful reading is the ordering. `explicit_dep` is the one step
that already carries a memo (RISFACT) and it is now the cheapest at 3.4 ms/call
against 5,764 calls — the memo works. Everything above it is the same recursive
descent re-entered again and again: `field_dep` -> `register_imported_symbol` ->
the composite's field loop -> `field_dep` …, with `methods` hanging off the same
node. 78% of qualified-type queries MISS, and a miss is what triggers the
descent.

### Fix in this session: RISDONE, the completed-registration memo

`register_imported_symbol` is idempotent **within one importer** — every branch
re-checks `already_bound` / `contains_key` before it writes — but nothing
remembered that a given tuple had already been registered, so a repeat re-ran
six linear surface-name scans and re-descended the entire field / method /
payload subtree beneath it. driver.spl issued 8,284 registrations for a far
smaller distinct set.

`registered_import_memo` (`hir_lowering/types.spl`) records
`{declaring module} {imported name} {local name} {materialize_enum}` for
registrations that **completed**, and the wrapper skips a repeat.

Two properties are deliberate and are what the spec pins:

- **It is not phase-invariant, unlike `explicit_dep_target_memo`.** The body
  writes into the IMPORTING module's symbol table, so the memo is owned by one
  importer: `begin_module` clears it (`context_helpers.spl`), and the wrapper
  independently drops it whenever `module_filename` names a different module.
  Carrying it across importers would leave the next importer with no binding at
  all.
- **A key is recorded only AFTER the body returns, never before.** Marking on
  entry would have been a free re-entrancy breaker, but it would also mark
  tuples whose body bailed out early against `imported_type_methods_in_progress`
  without finishing; those must stay retryable. Cycles keep being broken by the
  existing guards.

Observable mechanism counters, not wall clocks: `registered_import_skip_count`
on the lowerer, and `reg_skipped=` next to `reg_imported=` on the `[hir-prof]`
line. Pinned by `test/01_unit/compiler/hir/hir_import_registration_cost_spec.spl`
(mirrored in `test/unit/...`), which cannot pass on the pre-fix code.

### Also fixed: the last owner in `SymbolTable.define` (SCOPEIP)

`define` still did `var scope = self.scopes[i]` … `self.scopes[i] = scope`,
copying a value-type scope row (and its `symbols` Dict) on every one of the
1,529 defines driver.spl performs. That round trip survived only because
`self.scopes[i].symbols[name] = v` used to be rejected with *"semantic: invalid
assignment: complex field access not supported"*. Nested assignment targets are
supported now (`344f277cc45`) — verified against the deployed seed with a
10-line probe before the edit — so the row is written in place. The source-shape
contract in the same spec was updated to pin the new shape and to forbid the old
round trip.

### Still open

- The bisect table is NOT complete. The 2.7x between the two trees above is
  measured and reproducible from the two logs, but no single commit in
  `5020e8f3f45..d1fd6255ecd` has been isolated yet. Prime suspect on reading:
  `d757f7d70d0` ("freeze import item projections") deleted the re-export ROOT
  memo (`reexport_root_*`) outright as a correctness fix, which puts the whole
  re-export walk back on the un-memoized path that `glob` sits on top of — and
  `glob` is the sub-phase that grew 2.81x. Reinstating a correctly-invalidated
  version of that memo is the obvious next fix.
- **Neither fix in this session can be MEASURED on the deployed seed.** The
  `[hir-prof]` numbers are produced by the compiler doing the work, so a change
  to `src/compiler/**` shows up only once a compiler built from the patched tree
  is deployed. The evidence here is therefore the counter-based spec plus the
  mechanism argument; the wall-clock re-measure is owed after the next seed
  deploy.

## Sixth session (2026-08-22): what one first-time registration does for 40 ms

Run9 (`compiler.driver.driver`, memo `d954bcf0d5d`): HIR 254,987 ms, imports
243,413 ms, `reg_imported=2951` -> ~40 ms per FIRST-TIME
`register_imported_symbol_inner`. This session measured one registration in
isolation instead of the closure: a synthetic 3-package fixture (N structs with
3 fields, N free functions, N impls with 2 methods per package; dependency
fan-in capped at a group leader every 4 items so the field descent is bounded),
every export registered into ONE importer, single module, `--threads=2`, on the
deployed seed (`bin/release/x86_64-unknown-linux-gnu/simple`, the Rust seed).

### Breakdown before (N=100, 600 registrations, RIS slots + 3 new ones)

| slot | ms / calls | per call |
|---|---|---|
| wall per registration (avg, composites+callables) | 37,326 / 600 | **62 ms** (composites ~120 ms, callables ~5 ms) |
| `fields` (composite field-dependency loop, new slot) | 7,966 / 300 | 27 ms — of which `field_dep` (the actual calls) 715 / 900 = 0.8 ms |
| `project` (3 field projections + 2 dict stores, new slot) | 7,336 / 300 | 24 ms |
| `define` | 4,957 / 600 | 8 ms (2 ms when called from a spec) |
| `methods` | 2,262 / 300 | 7.5 ms |
| `scan` (six `module_surface_name_position` sweeps, new slot) | 260 / 609 | 0.4 ms |

`scan`, `callable_deps`, `declared_dep`, `explicit_dep`, `sigtype` are all
sub-millisecond: the candidate list in the lane brief (linear name scans,
surface re-resolution, COW clones of importer dicts, type-dep re-descent) is
NOT where the 40 ms is. Surface copies by value measured 0 ms / 100.

### The mechanism: a statement-cost cliff after a match-expression that returns

Bisecting inside `register_imported_symbol_inner` with one scalar `val` timed
into a spare slot: 0.03 ms at function entry, 0.05 ms after
`val composite = ...` and after the `same_owner` block, **12 ms** after

```
val kind = match composite.kind:
    case "class": SymbolKind.Class
    case "struct": SymbolKind.Struct
    case "actor": ...; return
    case other:   ...; return
```

An empty 3-iteration `for` / `while` after that line cost 8-10 ms; the same
loop before it cost nothing. So every statement after a match-EXPRESSION whose
arms contain `return` pays ~10 ms in this frame on the seed interpreter, and
the composite branch runs ~10 such statements. That is the ~100 ms of the
~120 ms composite registration, and the ~40 ms/registration average run9 saw.
(Seed-interpreter defect; filed separately below. The compiler-side fix is
shape-only.)

### Fixes (MATCHRET, IMPLIDX)

- **MATCHRET** (`module_import_registration.spl`): hoist the two early-exit
  diagnostics above the expression; `kind` becomes a plain `if` expression.
  Same diagnostics, same order, same HIR.
- **IMPLIDX** (`module_reexport_materialization.spl`, `types.spl`):
  `register_imported_type_methods_inner` swept every impl of the declaring
  module per imported type. `imported_impl_positions` indexes impl positions
  once per frozen surface (`{generation} {physical_index}` key, phase-invariant
  like `explicit_dep_target_memo`); counters `impl_index_build_count` /
  `impl_rows_visited`. Small on its own (~0.1 ms per impl row) but O(impls) per
  symbol -> O(impls^2) per module in the real closure.
- Three level-gated RIS slots kept: `scan`, `fields`, `project`.

### After (same fixture, same box)

| | before | after |
|---|---|---|
| per registration, N=100 avg | 62,210 us | **10,788 us** |
| `fields` | 27 ms | 1.5 ms |
| `project` | 24 ms | 0.3 ms |
| `define` | 8 ms | 2.8 ms |
| spec fixture N=40 x 3 pkgs (240 regs) | 85,429 us/reg (FAILS budget) | 14,420 us/reg |

Spec: `test/01_unit/compiler/hir/hir_import_registration_per_symbol_cost_spec.spl`
(mirrored in `test/unit/`): pins `impl_index_build_count == packages`,
`impl_rows_visited == composites`, and `<= 33,000 us` per registration (3x the
post-fix budget); verified red with the match-expression reinstated. Perf-gate
rows added to `scripts/check/check-perf-regression-tests.shs`.

### Remainder

- Composite registration is still ~15 ms: `methods` ~10 ms (2 methods x
  (`callable_deps` 0.9 + `sigtype` 0.4 + `define` ~2.8)) and `define` ~2-3 ms
  per call. `define` copies the Scope row (`val scope = self.scopes[id]`,
  including its `symbols` Dict) on the type-symbol first-write check; left
  alone because `lookup` documents `rt_dict_contains` under-reporting on that
  struct-valued dict.
- Seed interpreter: match-expression with returning arms makes every later
  statement in the frame ~10 ms. Other `val x = match ...: ... return` sites
  across the compiler will pay the same; a census is owed. The closure-level
  wall time is still owed after the next seed deploy (same caveat as session 5).

## Seventh session (2026-08-22): the whole stage1 compiler runs INTERPRETED

Seed `/mnt/data/seedperf/simple.1ffdfb58baf` (match-expr + me-call fixes in),
worktree `perf-hirwall` at `a32c3f3464f`. Two sessions were spent on
`define` (2-3 ms in context) and `methods` (~10 ms); both turned out to be the
same thing, and it is not in the compiler.

### The frame cliff is the module's import graph, and it is JIT-vs-interpreter

`SymbolTable.define` is **12 us** from a 4-line probe and **320-470 us** from
`register_imported_symbol_inner` -- same seed, same receiver, same arguments.
Bisected by hand: not the table size (flat to 30k symbols), not the nested
`self.symbols.define` receiver path (13 us), not expression vs statement
context, not 30 live locals, not call depth 24, not a 20k-entry outer object.
It is the probe file's `use` header: copying the 23 `use` lines of
`module_import_registration.spl` onto the unchanged probe makes the same
define cost 190-450 us. Single lines reproduce it: `use
compiler.frontend.flat_ast_bridge.{..}` -> 495 us, `..._Items.module_lowering.*`
-> 227 us, `..._AstExpr.accessors.{expr_get_arg_names}` -> 210 us,
`compiler.core.types.{int_to_str}` -> 53 us.

Every statement in the probe costs 0 ms JIT-compiled and ~2 us interpreted; a
call costs ~0 vs 8-16 us. The seed's `run` is whole-program JIT-or-nothing
(`driver/src/exec_core.rs:1006-1035`): one unsupported construct anywhere in
the closure prints `JIT compilation failed, falling back to interpreter` and
the ENTIRE program runs on the tree-walker. The real bootstrap log shows
exactly one such line:

    Cranelift JIT compile: Module error: function '_make_noop_lexer' loads a
    named function as a callable value; the JIT closure ABI has no tag-boxed
    representation for a bare function pointer

(`src/compiler/00.common/compiler_services.spl:168`, the port structs hold fn
refs; open P2 `jit_closure_abi_refuses_lambdas_and_miscompiles_fn_refs_2026-08-06.md`).
So **stage1 = the seed interpreting 1,500 compiler files at ~2 us/statement
and ~10 us/call.** That is the ~200x between 42 s and 0.2 s per module, and
it is why `define` is 12 us in a spec and 400 us in the compiler: the spec's
closure JIT-compiles, the compiler's does not. Every number in sessions 1-6
was measured on the interpreter; they stay valid, but none of them was a
compiler-side algorithm past session 5. The remaining "bugs" are statement
and call COUNTS on the interpreter.

### What one first-time registration is, in calls

Exclusive-time profiling (EXCL below) on the N=60 synthetic fixture, seed
`simple.hirwall-wip`: `callable_deps` body 0.48 ms params loop + 0.24 ms
return part per call = ~15 interpreted calls per parameter
(`qtype_raw_counted` x2 -> `lookup_qualified_type_raw` -> key concat -> has ->
bracket, plus the profile counter, plus `declared_dep`/`explicit_dep`), at
~10 us each. `methods` is two of those plus `sigtype` + `define`. Nothing left
is O(n) per call; it is ~300 small calls per registration.

### Fixes

- **NAMEIDX** (`module_import_registration.spl`, `types.spl`): the six linear
  `module_surface_name_position` sweeps per first-time registration become six
  Dict probes on a per-surface index built by one sweep per frozen surface
  (`{generation} {physical_index} {C|E|T|A|F|K} {name}` -> position, first
  occurrence wins like the scan). Counter `name_index_build_count`, pinned to
  `== packages` in `hir_import_registration_per_symbol_cost_spec.spl`.
  `scan` 229 -> 116 ms / 369 on the fixture (real surfaces are larger).
- **SCOPEROW** (`hir_types.spl`): `define` probes `self.scopes[id].symbols` in
  place instead of copying the Scope row (`VT_OBJECT_FIELD_CLONES` 1 per call).
  Resolves the open "Scope row copy" item; `lookup` keeps its
  `rt_dict_contains` bracket read unchanged.
- **EXCL** (`hir_phase_profile.spl`): `[hir-prof-excl]` line with EXCLUSIVE
  time per slot (child-time stack paired with the existing `now()`/`add()`
  sites, all audited balanced). The inclusive RIS slots recurse into each
  other and summed to 3-4x the module total; they could not say where the
  41 ms went.
- **PROFOFF** (`hir_phase_profile.spl`): every profiler site cost two
  interpreted calls with profiling OFF (`now()` -> `enabled()`); the cached
  "off" verdict now returns first. Fixture: 6,436 us/reg profile-on vs
  **4,216 us/reg profile-off** -- the profiler inflates its own numbers ~35%,
  which applies to every `[hir-prof]` line in this record.
- **Seed hot path** (`src/compiler_rust/compiler/src/`, gdb-sampled since
  `perf` is blocked here): (1) `record_decision_coverage_here` -- every
  if/elif/while/match decision resolved `current_coverage_file()` (thread-local
  borrow + String alloc) BEFORE the coverage-enabled check; 12 sites. (2)
  `capture_node_scope_shadows` computed the owner write-back target (a
  `global_binding` probe + `CURRENT_EXEC_MODULE` String clone) for every
  block-local `val` on every block entry; it now tests the prior value first
  (same writes in every case that wrote before). (3) `CowEnv::insert` skipped
  nothing: two SipHash removes on sets that are empty in the common frame.
  (4) `CowEnv`'s private per-frame maps (`overlay`, `tombstones`,
  `local_bindings`, `block_local_bindings`, `refreshed_globals`,
  `forwarded_globals`, `dirty_names`, `uninit_names`) on `ahash` (`FrameMap`
  / `FrameSet`); public signatures still hand out std maps; iteration order
  was already per-process random. Unit test
  `cow_env_frame_maps_round_trip_and_tombstone_clear`. Micro-probes, old ->
  new seed: 3 plain statements 17 -> 11 ms/3000, struct ctor 18 -> 12, free
  fn call 29 -> 24, me call 29 -> 24, call loop 2363 -> 1779 ms/300k. All 5
  cost/regression specs and the interpreter spec directory A/B pass.

### Not fixed, and the order of magnitude that is left

- The glob re-walk is NOT the glob cost: a memo-hit `register_imported_symbol`
  is 44 us, so re-walking a 200-name surface is ~9 ms, <1% of the 38 s glob
  on `driver_types.spl`. Glob time IS first-time registrations. The
  module-scoped glob memo was designed and dropped on that measurement.
- 87 `[hir-payload-origin-unresolved]` searches on the entry module are for
  builtin type names (`text` 29, `bool` 14, `Option` 12, `Any`, `char`,
  `Dict`) plus `i` 16 and `f` 6 -- which look like `i64`/`f64` with the digits
  stripped by whoever produced the payload name. Each pays the declaration
  probe + re-export walk + explicit-import sweep and finds nothing. Cheap
  individually; filed here, not fixed (the name-splitting half needs its own
  repro).
- The remaining per-registration cost is ~300 interpreted calls at ~10 us.
  The sampled profile after this session is a flat tail across the
  tree-walker (thread-local owner saves, owner-map hashing, per-call
  allocations, `publish_live_bound_globals` / `sync_owned_captured_globals`
  walking both frames' overlays on every `me` call). Getting to the 10-min
  stage1 target needs one of: the JIT closure ABI (P2 above) so the compiler
  stops running interpreted at all, a per-function JIT fallback instead of
  whole-program, or a pre-resolved-slot interpreter. None of those is a
  minimal fix.
