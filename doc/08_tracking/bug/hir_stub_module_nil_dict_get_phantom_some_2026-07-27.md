# Bug: nil Dict receiver — `.get()` returns phantom Some while `.len()` returns -1 (stub Module, stage-4 segfault lineage)

**Date:** 2026-07-27
Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
**Area:** native codegen (Dict nil-receiver methods) + Rust seed (HirLowering field-type inference)

## CORRECTION (2026-07-27, supersedes the analysis above)

Direct measurement falsifies the "header-only/partial modules carry nil decl
dicts" framing used throughout this doc (and the "Round 5" struct-field
map-copy theory it points to). The real defect is a `Dict<K, StructValue>.get()`
decode bug, unrelated to partial modules or struct-field copies:

- `Dict.len()` returns **-1** in native code for ANY dict — local or struct
  field, empty or populated. The "nil decl dict" signal (`functions.len() < 0`)
  this doc built its whole theory on was meaningless; it fired for every
  module (35,483 times in one stage-4 run), not just partial/header-only ones.
- A `Module` constructed IN PLACE with `functions: {}` already reads `fns=-1`,
  proving no map copy and no partial-parse state is involved — the signal is
  an artifact of `.len()` itself.
- The actual defect: `Dict<K, StructValue>.get()` on a HIT returns a non-nil
  Option whose payload is corrupt — `.unwrap()` or a field read segfaults.
  Misses correctly return nil. `contains_key()`, `keys()`, and index reads
  `d[k]` are all correct. `Some(d[k])` round-trips correctly (including
  Option-param passing).
- For `Dict<text,i64>`, `.get()` returns the still-BOXED value (7 came back as
  56 = 7<<3) — the decode is missing/wrong specifically on the `.get` path,
  while `d[k]` decodes correctly.
- Stage-4 crash mechanism: `register_imported_symbol` did
  `imported_mod.traits.get(name)` then `lower_trait(as_trait.unwrap())`; on a
  HIT (std.io.traits' `Read`) the corrupt Option segfaulted — nothing to do
  with the module being partial/header-only.
- Fix landing now: all struct-valued dict lookups in
  `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` rewritten to
  `contains_key` + index reads; the guard rounds and the module-global
  registry experiment below are being reverted as unnecessary.
- See the new primary bug docs:
  `doc/08_tracking/bug/native_dict_get_struct_value_corrupt_option_2026-07-27.md`
  and `doc/08_tracking/bug/native_dict_len_returns_minus_one_2026-07-27.md`.

## Summary (original analysis — superseded, kept for history)

During stage-4 bootstrap, `HirLowering.register_imported_symbol` operates on a
stub `Module` whose dict fields (e.g. `imported_const_decls`) were never
initialized. The seed nil-fills omitted struct-init fields, so the field holds
nil. Two root defects:

1. **Native codegen, phantom Some:** `.get(key)` on the nil Dict receiver
   returns a phantom non-nil Option (a "Some" wrapping garbage) while `.len()`
   on the same receiver returns -1. Downstream code trusts the phantom Some and
   dereferences garbage — the stage-4 bootstrap segfault lineage. The
   fail-closed contract is: `.get()` on a nil receiver must return nil, and
   `.len()`/`.get()` must agree (len() <= 0 implies get() -> nil).

2. **Seed field-type inference, hair-trigger control-flow sensitivity:** the
   seed's field-type inference in `HirLowering.register_imported_symbol` is
   sensitive to the guard's control-flow shape — four distinct guard shapes
   each broke with `cannot infer field type ... imported_const_decls`, making
   it impossible to guard the nil receiver at the call site without tripping
   inference.

## Repro spec

`test/01_unit/compiler/hir/nil_dict_receiver_phantom_option_spec.spl` — a
deliberately RED spec pinning the desired fail-closed contract (defect 1):

- `it "nil dict receiver returns nil from get, never a phantom value"` —
  `.get("k")` on a nil-filled Dict field must be nil.
- `it "len and get agree on a nil dict receiver: non-positive len implies nil
  get"` — if `.len() <= 0` then `.get()` must be nil.

The spec constructs a `StubModule` with an omitted (hence nil-filled)
`imported_const_decls: Dict<text, i64>` field, mirroring how the compiler hits
the receiver. It is EXPECTED RED under native codegen until the nil-receiver
fix lands; per repo convention for filed defects it stays visibly red (no
`skip()` — precedent: `rv32_trap_completeness_spec.spl`). Interpreter
semantics may differ from native; the spec's value is as the native-contract
pin.

## Refined root cause (SIMPLE_BOOTSTRAP_DIAG run)

The "stub" modules are **header-only registry entries**: files OUTSIDE the
entry closure get parsed for name/imports/exports only, so their decl dicts
are nil while `.name`, `.imports`, `.exports` read correctly. Diag evidence —
the swept siblings themselves are partial:

```
[reexport-chase] mod=std.nogc_sync_mut.io.pipe wanted=Read ... found=true
                 mname=src/std/nogc_sync_mut/io/pipe.spl fns=-1
```

`resolve_package_sibling_symbols` sweeps ALL `modules_by_name` keys under the
package prefix — including partial entries — and the facade-glob chase then
walks the partial module's imports into `std.io.traits` (also partial), where
the trait arm unwraps the phantom.

## Mitigation (landed 2026-07-27)

Skip partial modules in the sibling sweep
(`resolve_package_sibling_symbols`): register a sibling's glob symbols only
when `(sibling_mod ?? module).functions.len() >= 0`. A partial sibling
contributes no compiled symbols, so this is semantically clean — packages'
bare cross-file calls only ever resolve against closure members.
`register_imported_symbol` stays byte-pristine.

Why not guard in `register_imported_symbol`: FOUR shapes all break the seed
build with `hir: Unsupported feature: cannot infer field type ... field
'imported_const_decls'` (a pristine-file control build compiles clean, so the
coupling is real, not cache poisoning):
1. `var ... = nil` + conditional assign on all six lookups
2. single-line if-expression initializers on all six
3. single-line if-expression on the trait lookup alone (fresh cache)
4. `traits.len() > 0` added to the elif condition, and separately as a
   nested if inside the arm around `lower_trait` (fresh caches)
Meanwhile an added `eprint` statement at existing nesting compiled fine. The
seed's field-type inference for `imported_const_decls` is hair-trigger
sensitive to control-flow shape in this one function — that fragility
deserves its own fix.

The phantom-Some hazard remains for any OTHER path that hands a partial
module to `register_imported_symbol` (direct imports of out-of-closure
modules, glob-import path); the real fix below covers those.

## Real fix

- Make native nil-receiver `Dict.get` return nil (align with `.len()`'s
  defined -1 behavior), with a deliberate-red spec on a nil-dict receiver.
- Root-cause why the `std.io.traits` Module object is a stub with nil dicts at
  sweep time (alias-key registration path in `resolve_module_key`?).
- Harden seed field-type inference so a guarded initializer among sibling
  `val`s does not detach `imported_const_decls` from its inferred type.

## Repro

Stage-4 native-build of `src/app/cli/main.spl` (full closure, llvm backend) at
main ≥ d07208d1c4f without the mitigation; crash at HIR module 32.

## Related

- `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md` (Lane H)
- `reference_jit_option_i64_value3_none_collision` (memory)
- Trap D note in `module_lowering.spl` `lower_parser_module_unstub`

## Second site: direct-import path (2026-07-27, same day)

With the sibling-sweep guard in place, the stage-4 repro cleared the original
crash point (env_ops.spl, HIR module 32) and 69 modules, then segfaulted in
`resolve_import_symbols` for `src/lib/nogc_async_mut/database/test.spl` — the
same phantom-Some family via `register_imported_symbol`'s six decl-dict
`.get()` lookups on a header-only imported module. Second guard: early-return
at the top of `register_imported_symbol` when
`imported_mod.functions.len() < 0`, falling through only to the re-export
chase (header parsing does populate imports/exports). This gate covers every
caller (direct import, glob, sibling sweep, re-export recursion).

## Remaining latent sites (audit, 2026-07-27) — not yet observed to fire

1. `register_glob_imported_symbols` (module_lowering.spl:687-717): six `.keys()`
   on imported_mod dicts; reached from the glob path in
   `resolve_import_symbols` (:800) whose `modules_by_name.get()` lookups
   (:745/:783/:793) are ungated. Highest residual risk.
2. `hir_module_declares_item` (:74-84) via `find_reexport_source` (:602/:630):
   `.contains_key()` on ungated next-hop modules — the re-export chase can hop
   into another header-only facade.
3. `lower_module` imported-enum harvest (:1301-1315): `.enums` reads on the raw
   `modules_by_name.get(imp.module)` (:1298), no partial gate.

Root cause + one-site decode fix proposal:
`native_nil_dict_get_phantom_option_rootcause_2026-07-27.md` (nil sentinel 3
shifted to phantom 0 by decode_runtime_value's integer arm).

## Focused sub-builds relied on the phantom (round 4, 2026-07-27)

With all six guards in, stage-4 completes HIR for all 1738 files with no
segfault/spin, but focused template-specialization sub-builds
(compiler.driver.pipeline_fn / compile_specialized_template) fail loud:
`unresolved name: OptimizationConfig / CompiledUnit`. DIAG shows their import
targets are header-only in the focused registry BY DESIGN (`fns=-1`), and the
wanted names are DECLARED there (not re-exported), so the chase finds nothing.
Pre-guard, the phantom Option always hit the class arm first, so every
partial-module import accidentally registered as an opaque Class symbol —
load-bearing behavior for focused builds. Round-4 fix: when the partial-module
chase fails, deliberately register an opaque Class-kind symbol (define +
rename only, no decl deref, no type-method registration).

## Round 5: the registry itself was corrupted (root of the whole family)

get-vs-index instrumentation proved the corruption is NOT in `.get()`: index
reads from `HirLowering.modules_by_name` see the same nil dicts
(`idx_fns=-1 idx_forder=9`). The driver's `ctx.modules` map is intact
(`ctx.modules[name]` at lowering time has real dicts — bodies compile), but
the copy of that map into the HirLowering struct FIELD nil-fills every Module
value's nested Dict fields while array fields survive (native aggregate
deep-copy defect). Import resolution only ever read the corrupted field, so
every import resolved through the phantom-decode accident. Fix: module-global
registry (`module_registry.spl`, accessor-fn pattern) mirrored by the driver
at parse time via plain arg-pass + dict-insert (both preserve nested dicts);
seven lookup sites refetch through it. Guards from rounds 1-4 remain as the
safety net for genuinely-absent entries.
