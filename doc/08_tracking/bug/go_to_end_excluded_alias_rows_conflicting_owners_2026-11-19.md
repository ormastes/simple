# go-to-end: one HIR failure in a package kills the whole MIR phase ("conflicting owners") + stale `Module` import in app.io.jit_sffi

- Status: fix-implemented (source fix verified natively; compiler fix unit-specified, not yet proven in a rebuilt Stage 2)
- Severity: P1 (blocked the Phase 4 full-CLI native build: 0 objects)
- Found: 2026-11-19, Phase 4 run `cli-i15` (source `9f89b7d0b55`, 4032 modules, entry
  `src/app/cli/_CliMain/main_and_help.spl`, cranelift, `--go-to-end`)
- Binary used for the reduced repro: Stage 2 admitted from `24941411f54` (aarch64, cranelift)

## A. Stale import: `compiler.frontend.parser_types.{Module}`

`5de6f3c56e8` (2026-07-30, PTR1) renamed nine parser structs to `Parser*`;
`struct Module` became `struct ParserModule` (`src/compiler/10.frontend/parser_types.spl:26`).
`src/app/io/jit_sffi.spl:24,147` kept the old name, as did five test files.

```
[hir-reexport-chase-unresolved] facade=compiler.frontend.parser_types item=Module ... importer=src/app/io/jit_sffi.spl
[hir-fatal] ... HIR lowering error in src/app/io/jit_sffi.spl: unresolved type: Module
```

The self-hosted resolver is right: no module declares or re-exports that name.
`app.io.__init__` re-exports `app.io.jit_sffi`, so the failure excluded the CLI
entry transitively.

Fix: import and use `ParserModule` (same change in the five test files).

Not established: whether the Rust seed accepts the stale import. No seed binary
on the host could load the tip tree (newest is 2026-11-15), so no resolution
difference is recorded here.

## B. Excluded alias rows give one file two owners

`src/compiler/80.driver/driver_pipeline_lowering.spl` (`mir_setup:physical_owners`)
pushed the row's LOGICAL NAME as the owner of every go-to-end excluded row.
Exclusion is keyed by logical name, and one file can hold several inventory
rows: `app.io` and `app.io.__init__` are both `src/app/io/__init__.spl`. Held
rows use `HirModule.name` (the file path), so aliases fold; excluded rows did
not, and `driver_mir_physical_source_indices_v1`
(`driver_mir_physical_owners.spl:44`) returned

```
MIR physical source has conflicting owners: .../src/app/io/__init__.spl
```

which fails the entire MIR phase, defeating go-to-end. It is not a recipe
error: the overlapping `--source` roots are not involved.

Five-file repro (Stage 2 from `24941411f54`, `p4_s2.sh`, cranelift):

```
src/app/p4probe/__init__.spl   export use app.p4probe.bad.{bad_fn}
src/app/p4probe/bad.spl        fn bad_fn() -> i64:  var m: Dict<text, NoSuchTypeP4> = {} ...
src/app/p4probe/good.spl       fn good_fn() -> i64: 7
src/app/p4probe_main.spl       use app.p4probe.{bad_fn}; use app.p4probe.good.{good_fn}

[go-to-end] failed stage=hir_dependency module=app.p4probe.__init__
[go-to-end] failed stage=hir_dependency module=app.p4probe
[first-compile-error] MIR physical source has conflicting owners: src/app/p4probe/__init__.spl
```

Fix: `driver_mir_excluded_owner_v1(row_path, logical)` stands the row path in
(both the checked-entry-projection and the admitted-inventory route). Spec:
`test/01_unit/compiler/driver/mir_physical_owners_spec.spl`.

## Open: sibling variant

Same repro with the unresolved type in `bad_fn`'s SIGNATURE: `app.p4probe.__init__`
fails at stage `hir` and is excluded, but its alias `app.p4probe` is not, and
MIR setup stops with

```
MIR physical ownership missing HIR for app.p4probe
```

The exclusion set records one spelling of a failed module, not every inventory
row of that file. Not fixed here.
