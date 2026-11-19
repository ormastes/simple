# `std.database.test_extended` resolves to a stale file facade, not the package `__init__` — full-CLI Stage 2 dies on `unresolved type: TestStatusCounts` (2026-11-19)

- **Status:** WORKED AROUND (stdlib facade sync); compiler-side diagnostic OPEN
- **Area:** native entry-closure module resolution (`std.X` tier flattening) +
  HIR re-export chase; stdlib `database/test_extended` facades
- **Found:** Phase 4, native Stage 2 (integ22,
  `pinned-e1b8cc353599/.../stage2-admitted/simple`) compiling the full CLI from
  release tip `e1b8cc35359`

## Symptom

```
failed stage=hir module=lib.nogc_sync_mut.test_runner.test_db_compat: ... unresolved type: TestStatusCounts
failed stage=hir module=app.test_runner_new.test_query_cli: ... unresolved type: TestStatusCounts
failed stage=hir module=app.traceability.query_evidence_testdb_v1: ... unresolved type: TestStatusCounts
failed stage=hir module=app.traceability.test_query_scope_v1: ... unresolved type: TestStatusCounts
failed stage=hir_dependency module=app.cli._CliMain.main_and_help: not lowered: imports (transitively) a module whose HIR failed
```

`main_and_help` excluded ⇒ no full-CLI binary.

## Root cause

Every `use std.database.test_extended.{...}` importer resolves the package
spelling to the FILE `src/lib/nogc_async_mut/database/test_extended.spl`, not
to `src/lib/nogc_sync_mut/database/test_extended/__init__.spl`:

- `std.X` flattening tries the tier families in
  `source_root_std_family_order_v1()` order (`nogc_async_mut` first,
  `src/compiler/00.common/source_root_resolution.spl:9`), and HIR
  `resolve_module_key` tries the literal key before `X.__init__`
  (`src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl:1331`).
  Both tiers carry a `test_extended.spl` file AND a `test_extended/` package,
  so the file in the first tier wins. Confirmed from the build log of the
  fixture below: the closure parses `nogc_async_mut/database/test_extended.spl`
  and never parses either `test_extended/__init__.spl`.
- That file facade still listed only the original nine record types. PR #10409
  added `TestStatusCounts` and 14 other wrappers to `types.spl` and to the two
  `__init__.spl` facades, and PR #10467 to the async `types.spl` — but never to
  the two `test_extended.spl` file facades, which nobody knew were the live
  ones.
- The re-export chase (`find_reexport_source_walk`) therefore finds no import
  item, no export route and no package-sibling match on the file facade, emits
  `[hir-reexport-chase-unresolved] ... item=TestStatusCounts`, registers
  nothing.
- Normally that miss is still silently rescued by the closure-wide
  unique-owner fallback (`try_register_bootstrap_global_symbol`,
  `module_import_registration.spl:1262`): the name has exactly one declaring
  surface, so it binds anyway. The full-CLI closure ALSO loads
  `src/app/stats/test_status.spl`, which declares an unrelated
  `struct TestStatusCounts`. Two owners ⇒ the fallback gives up ⇒ hard
  `unresolved type` on the importer (`test_db_compat`) and on every module
  lowering a signature that mentions it through
  `RunnerTestDb.test_count_by_status()`. This is why small closures stayed
  green and only the full CLI broke (measured: the same fixture without the
  `app.stats.test_status` import builds and runs while still printing the
  chase-unresolved receipt).
- `test_extended/database.spl` imports from `std.database.test_extended.types`
  (a leaf module, no file/package ambiguity), which is why it resolves.

## Workaround (this change)

`# @workaround bug=test_extended_file_facade_shadows_package_init_2026-11-19`
in both `src/lib/{nogc_sync_mut,nogc_async_mut}/database/test_extended.spl`:
the type lists now match `test_extended/__init__.spl`, and the async file gained
the explicit `export use` blocks the sync file already had (the two files are
now byte-identical).

## Compiler-side fix still owed

A module path that names BOTH `X.spl` and `X/__init__.spl` (in one tier or
across flattened tiers) is silently resolved to whichever is probed first. That
should be an `Ambiguous` result (the enum already exists:
`SourceRootResolutionV1.Ambiguous`) or at minimum a diagnostic naming both
files, so a facade edit that lands in the shadowed file cannot silently miss.
Unblock condition for removing the workaround: either the duplicate
`test_extended.spl` files are deleted in favour of the package `__init__`, or
the resolver rejects the dual shape.

## Evidence

Fixture: `test/fixtures/test_extended_facade_status_counts/main.spl` (imports
`TestStatusCounts` through the package facade and calls
`test_count_by_status()`), native-built with the integ22 Stage 2 compiler,
cranelift, `SIMPLE_BOOTSTRAP=1 ... --entry-closure`, under
`systemd-run --user --scope -p MemoryMax=16G -p MemorySwapMax=0`, source tree
= release/1.0.0 `17b0a282794` (no diff vs `e1b8cc35359` under
`src/lib/*/database`, `src/lib/nogc_sync_mut/test_runner`, `src/compiler/20.hir`).

```
SIMPLE_BOOTSTRAP=1 SIMPLE_NATIVE_GO_TO_END=1 SIMPLE_FILE_WORKERS=0 SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 \
  systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 timeout 1500 \
  $S2 native-build main.spl --backend=cranelift --entry-closure --cache-dir cache -o out
```

RED (unpatched facades):
```
[hir-reexport-chase-unresolved] facade=lib.nogc_async_mut.database.test_extended item=TestStatusCounts local=TestStatusCounts importer=main.spl: ...
[ERROR]   HIR lowering error in main.spl: unresolved type: TestStatusCounts
[ERROR]   HIR lowering error in main.spl: unresolved name: TestStatusCounts at main.spl:21:18
[go-to-end] failed stage=hir module=main: HIR lowering error in main.spl: unresolved type: TestStatusCounts
build rc=1
```

GREEN (this change): no `hir-reexport-chase-unresolved` / `unresolved` line;
the closure parsed `src/lib/nogc_async_mut/database/test_extended.spl`.
```
build rc=0
run rc=0
total=0 passed=0 failed=0 skipped=0
total=3 passed=2 failed=1 skipped=0
stats source=doc/08_tracking/test/test_result.md
```

Control: the fixture WITHOUT the `app.stats.test_status` import on the
unpatched tree printed the same chase-unresolved receipt yet built and ran
(`build rc=0`, `run rc=0`) — the unique-owner fallback masked the miss.

Follow-up (generalization check, not in this change): a guard that the
`test_extended.spl` file facades and `test_extended/__init__.spl` export the
same name set, until the dual shape is removed.
