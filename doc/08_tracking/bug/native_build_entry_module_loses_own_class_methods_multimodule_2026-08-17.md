# native-build: an entry module with any `use` import loses its OWN class methods

- **Filed:** 2026-08-17
- **Severity:** P1 — this is not a trailing-defaults edge case. It is a general
  break of concrete-class instance-method dispatch for every multi-module
  `native-build`, i.e. for essentially every real program.
- **Status:** OPEN, diagnosed and bisected, unfixed

## Symptom

```
MIR lowering error: unresolved method call: bump
```

`bump` is an ordinary instance method, defined in the very module being compiled.

## Bisect result — the actual trigger

Reduced from `test/fixtures/native_trailing_default_param/main.spl`. The failing
condition is far more general than the fixture it was found in:

> **Any concrete-class instance-method call, in an entry module that has at least
> one `use` import, under multi-module `native-build`.**

Falsifying controls, all measured:

| shape | result |
|---|---|
| entry module with a `use` import, `w.bump(1)` | **FAIL** — unresolved method call |
| same call, entry module with NO `use` import | PASS |
| trailing default args removed entirely | still FAIL |
| all args supplied explicitly | still FAIL |
| `static fn` on the same class (`Widget.stat`) | resolves (`found=true`) |

So trailing defaults are **irrelevant** — they were a red herring from the
fixture's name. What matters is the presence of a cross-module import at all.

The probe trail shows the entry module's own methods failing static lookup and
falling through to the unresolved arm:

```
[mir-method-call] resolution-arm=unresolved method=bump
[mir-method-call] unresolved-static method=bump srn='' disc=1337030607 found=false
[mir-method-call] unresolved-static method=stat srn='' disc=1337030607 found=true
```

## Locus

`src/compiler/35.semantics/resolve_strategies.spl:133-138` and the symbol-table
population feeding it. When the multi-module closure is built, the entry module's
own class methods are not present in the table it consults — the module loses its
own members in the closure that was supposed to *add* to them.

## Two prior misdiagnoses, both refuted with evidence

This defect cost four-plus rounds across several lanes. Recording the refutations
so nobody re-walks them:

1. **"`undefined variable Widget` in native-build MIR lowering."** REFUTED —
   `grep -n Widget` over the full 2153-line native-build log returns **zero**
   hits.
2. **"`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:49`, a module-level
   `var` with an initializer that native-build's pure-Simple parser rejects
   (`expected Fn, found Assign`) while the Rust seed accepts it."** REFUTED — that
   text appears nowhere in the log. It had already been refuted once by ablation
   in another lane.

## A second, independent defect found alongside it

The real error was invisible for days because the build driver **swallows it**:
`build_outcome.spl` never prints a unit's `diagnostics` field. The outcome summary
reports `ERROR=1` and names the failing unit, and stops there:

```
===== build outcome summary =====
OK=1
ERROR=1
ERROR: 1 unit(s)
  - test.fixtures.native_trailing_default_param.main
===== end build outcome summary =====
```

A build driver that knows why a unit failed and does not say is how a
one-line diagnosis became a multi-lane investigation. Worth its own fix
regardless of this bug.

## OPEN QUESTION — possible shared root with the stage-3 blocker, UNPROVEN

`doc/08_tracking/bug/stage3_post_parse_surface_window_has_no_receipts_2026-08-17.md`
describes a stage-3 failure at `phase=hir` in which symbol lookups resolve to
**foreign** symbols. "A module loses its own members in a multi-module closure" is
the same *family* of complaint, one phase earlier in the pipeline.

**This is explicitly NOT an assertion that they are the same bug.** No shared
root cause has been demonstrated, and the two could easily be independent defects
in different tables. It is recorded because whoever fixes either one should read
the other first: if the symbol-table construction for the multi-module closure is
the common ancestor, one fix closes both, and if it is not, ruling that out is
cheap and worth writing down.

## Guard

`scripts/check/check-native-trailing-default-param.shs` fails on this. Its name
now under-describes what it catches — it is, in effect, the repo's only gate on
multi-module `native-build` instance-method dispatch. Consider renaming it when
this is fixed, and note that the guard is only meaningful where `bin/simple`
exists; see
`doc/08_tracking/bug/guard_silent_nonzero_exit_no_verdict_line_2026-08-17.md`.

## 2026-08-17 re-check (independent lane) — STILL OPEN, reproduction blocked

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
size 59537240, mtime 2026-08-17 12:58:51 UTC.

Locus unchanged: `try_instance_method` is still
`src/compiler/35.semantics/resolve_strategies.spl:133-138`, a single
`symbols.lookup_method_in_type_raw` with a `nil` fallthrough — no change since
this row was filed.

**The `unresolved method call: bump` symptom could not be reproduced today**, and
the reason is NOT that it is fixed: the native-build worker never reaches MIR
lowering. It is the interpreted whole-compiler worker
(`bin/simple run src/app/cli/native_build_worker.spl ...`) and it aborts on a
failed allocation during `parse`. Two concurrent runs of this row's own fixture
were observed live on this host:

```
$ ps -eo pid,etimes,pcpu,rss,args | grep native_build_worker
3700449  599  90.7  17314092  ... --entry test/fixtures/native_trailing_default_param/main.spl ...
3703879  537  88.5  15549864  ... --entry test/fixtures/native_option_eq_representation/main.spl ...
```

17 GiB and 15 GiB RSS respectively, still climbing, on two-file fixtures. A
one-module no-import fixture bounded at `ulimit -v 12000000` aborted outright
with `memory allocation of 2147483648 bytes failed`.

So `check-native-trailing-default-param` cannot give this row a verdict at
present. Detail, and the driver-side fix that stops that abort being reported as
a `7200s` timeout:
`doc/08_tracking/bug/native_build_source_closure_zero_sources_2026-08-17.md`.

**Revalidated 2026-11-02: still plausible because OPEN, diagnosed and bisected, unfixed; no merged fix commit with a passing regression is cited in this doc.**

## Lane note 2026-11-03 (wl01 lane)
Deferred: the existing row records a source repair/workaround already exists and needs a rebuilt producer plus native requalification run; no native-build producer is runnable on this lane.

## Lane note 2026-11-03 (comp-entrymeth2): interpreter harness does NOT reproduce; locus premise refuted

Spec: `test/01_unit/compiler/50.mir/entry_module_own_class_method_with_import_spec.spl`
(HIR+MIR lowering of a 2-module closure, entry class `Widget` with instance
`bump` and `static fn stat`, entry `use`-imports the helper). Run with the seed
(`bin/simple.exe test <spec>`): 3/3 pass. Control (no import) passes; the import
case reports NO `unresolved method call` with providers `[helper, main]` or
`[helper]`; the non-vacuity case (`w.nope_missing(1)`) does report it, so the
harness would see the defect if it were present.

Consequences:
- The failure is NOT in source-level symbol registration that this harness
  exercises (`SymbolTable.define` owner-qualified `Type::method` rows,
  `lookup_method_in_type_raw`, `struct_method_syms` from `module.impls`). Those
  resolve the entry class's own instance method in a multi-module lowering.
- `35.semantics/resolve_strategies.spl:try_instance_method` is not the reaching
  path: the failing arm is MIR `MethodResolution.Unresolved` recovery in
  `50.mir/_MirLoweringExpr/method_calls_literals.spl` (~4487-4797).
- Remaining suspects are native-driver-only: the `--entry` closure lowering in
  `80.driver/driver_pipeline_lowering.spl` (ambient bootstrap branch of
  `lower_module` returns before the `module.impls` -> `struct_method_syms`
  registration at `module_lowering.spl:~3225`), and native-only corruption of the
  recovery inputs (`struct_value_syms`, discriminant garbage 1337030607).
- Status: still OPEN, no fix landed. Verification needs a native/stage3 run:
  `test/fixtures/compiler/native_entry_own_class_methods/` (expected
  `w.n=42`; known-bad `unresolved method call: bump`) with
  `SIMPLE_MIR_METHOD_CALL_TRACE`-style `[mir-method-call]` probes enabled, and
  check whether `struct_method_syms["Widget::bump"]` exists when the entry is
  lowered with `SIMPLE_BOOTSTRAP=1`.

## 2026-11-07 mir-p2: driver-shaped feed does not reproduce either

- Added a case to `entry_module_own_class_method_with_import_spec.spl` that
  calls `lower_module_transient_scoped(main, [main, helper], true)` — the exact
  `driver_pipeline_lowering.spl` call (whole closure as feed, entry included,
  lazy provider session). 4/4 green on the seed interpreter.
- `SIMPLE_BOOTSTRAP=1` makes this harness vacuous: the non-vacuity case fails
  (the ambient branch of `lower_module_guarded_v1` returns before the
  `module.impls` -> `struct_method_syms` pass and reports no unresolved call),
  so a bootstrap-mode interpreter run cannot discriminate this defect.
- Conclusion: the defect is in the natively compiled compiler (values such as
  the `disc=1337030607` garbage point at native miscompile of the recovery
  inputs), not in the lowering logic as interpreted. Needs a stage3 producer
  and the `test/fixtures/compiler/native_entry_own_class_methods/` run. OPEN.

## Reopened 2026-11-07

PR #7408 changed these rows on seed-only evidence, which is insufficient. Stage3 (native) still fails: on s3_fable54m, s3_fable56 and s3_fable57s the 12-line fixture C:/dev/p3new/s3sanity/root/test/s3sanity/vb_mm1.spl (struct + impl method + one call) fails during HIR lowering with `[simple-runtime][error] rejected invalid array handle before dereference` followed by `unresolved method call: get route=runtime-fallback key=test.s3sanity.vb_mm1.Custom::get struct_method_syms=yes record_instance_method=n/a lookup_method_in_type=no receiver_has_type=false`. The same file without the call passes; fixture test/fixtures/compiler/native_entry_own_class_methods has the same shape. Status: OPEN, root-cause lane in progress.

## Fix 2026-11-08 (lane-f-entrymeth) — source workaround landed, native verification pending

**Root cause (upstream of the vb_mm1 recovery region).** HIR lowering resolved
only STATIC methods (`declared_static_method_resolution`) and handed every
instance call (`w.bump(1)`, `custom.get()`) to MIR as
`MethodResolution.Unresolved` with an untyped `NamedVar` receiver (the Ident arm
never attaches `has_type_`). Under the interpreter that is harmless: MIR's
Unresolved-owner recovery (`50.mir/_MirLoweringExpr/method_calls_literals.spl`,
`unresolved-receiver` .. `unresolved-owner-done`) resolves it. Natively that
recovery is the region the frozen stage2 miscompiles — s3_fable64 (f64t2 run,
`C:/dev/p3new/s3sanity/out_f64t2/vb_mm1/native-build.log.err`) still shows
`resolution-enter unresolved=true` -> `unresolved-owner-get` -> `route=runtime-fallback
... struct_method_syms=yes struct_method_sym_id=7 ... receiver_has_type=false`,
with no `use` import at all (vb_mm1.spl). The import in this row's fixture was
never the trigger; every same-module instance call is exposed. The
`lookup_method_in_type=no` probe flag is a probe artefact (it looks the
module-qualified owner text up with `lookup_or_invalid`), not evidence about
`lookup_method_in_type_raw`.

**Change.** Resolve `local.method()` at HIR time through raw-scalar lookups so
MIR takes the plain `InstanceMethod` arm (the same arm the 35.semantics resolver
feeds) and never enters the recovery:
- `20.hir/hir_symbol_table_methods.spl`: new
  `binding_declared_record_owner_scalar_raw(raw) -> i64` — Struct/Class owner id
  of a Variable/Parameter symbol's declared `Named` type, else -1; no
  `HirSymbol?`/`HirType?` Option crosses a call boundary.
- `20.hir/hir_lowering/_Expressions/expression_core.spl`: new
  `declared_instance_method_owner_raw_v1(receiver_kind, method, static_resolution) -> i64`
  (owner id only when the static resolution is `Unresolved`, the receiver is a
  binding whose owner is known — declared type, or, since `var w = Widget(...)`
  is still `Infer` at HIR time (measured: `binding_type=Infer stored_type=nil`),
  the constructor spelling the Let lowering already recorded in
  `local_struct_types` resolved through `lookup_or_invalid` — and
  `record_instance_method_scalar_raw(owner, method)` finds the owner-qualified
  `Method`); both MethodCall arms (pre-dispatch arm A
  and arm B) rebuild `MethodResolution.InstanceMethod(owner, method)`
  statement-shaped from the two raw ids; `declared_exists_check_type` gained the
  matching `InstanceMethod` arm so `if val x = w.find()` keeps its declared type.
- Workaround tag at both new helpers:
  `# @workaround bug=native_build_entry_module_loses_own_class_methods_multimodule_2026-08-17 reason=...`.
  Static, enum-constructor, Optional, generic, trait and UFCS receivers answer -1
  and keep their previous path; an undeclared method stays `Unresolved`.

**Specs (seed interpreter, `bin/simple.exe test`).**
- NEW `test/01_unit/compiler/20.hir/entry_module_instance_method_hir_resolution_spec.spl`:
  before the fix 1/4 (bump/peek `unresolved`, owner check fails); after 4/4 —
  `me bump` and plain `fn peek` on `var w = Widget(...)` resolve to
  `InstanceMethod` whose owner is `Widget` (not the same-leaf-name `Other.bump`,
  method symbol `app.main.Widget::bump`), `Widget.stat` stays on the static arm,
  `w.nope_missing` stays `Unresolved`.
- EXISTING `test/01_unit/compiler/50.mir/entry_module_own_class_method_with_import_spec.spl`:
  4/4 before and after; it now exercises the HIR `InstanceMethod` route into MIR
  instead of the recovery.

**Still unverified (native).** No stage3 rebuilt from this source exists; the
fixture `test/fixtures/compiler/native_entry_own_class_methods/` (expected
`w.n=42`) and `C:/dev/p3new/s3sanity/root/test/s3sanity/vb_mm1.spl` must be
re-run with a producer built from this change. The vb_mm1 recovery region itself
was not edited (owned by the vb_mm1 lane).
