# A glob-imported PRIVATE fn lowers to an unmangled extern instead of failing to resolve

## Open 2026-11-11 — LIVE (interpreter leg re-confirmed permissive), keep OPEN (lane ne10; see addendum)

- **Status:** OPEN (2026-09-13; re-confirmed LIVE 2026-11-11 lane ne10). Worked around at the call site, NOT fixed.
- **Layer:** Rust seed, name resolution -> MIR/LLVM lowering.

## Shape

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` glob-imports
both `compiler.mir._MirLoweringExpr.expr_dispatch.*` and
`compiler.mir._MirLoweringExpr.switch_operators_calls.*`. Each of those modules
defines its own **private** (non-`pub`, leading-underscore) helper

```
@always_inline
fn _sffi_enum_discriminant(value: Any) -> i64:
```

Neither is exported, so the name is not in scope in the importer. The expected
behaviour is a compile-time unresolved-name error. What the seed does instead is
emit a call to the **unmangled** symbol `_sffi_enum_discriminant` (C-mangled to
`__sffi_enum_discriminant` on Mach-O), which nothing defines. The failure is
therefore deferred all the way to the native link:

```
Undefined symbols for architecture arm64:
  "__sffi_enum_discriminant", referenced from:
      _compiler__mir___MirLoweringExpr__method_calls_literals__MirLowering.mir_type_is_scalar_numeric
     (maybe you meant: _compiler__mir___MirLoweringExpr__expr_dispatch___sffi_enum_discriminant, ...)
```

The linker's own "maybe you meant" list shows the four sibling modules each
emitting a correctly per-module-mangled copy, which is what makes the unmangled
reference obviously wrong rather than a missing runtime symbol.

## Why nobody caught it

The interpreter resolves the glob-imported private name permissively, so
`d5b5d9f3408` (which introduced `mir_type_is_scalar_numeric` and its ten
`_sffi_enum_discriminant` call sites) passed every interpreter-tier check. Only
a native link of the Stage-2 closure surfaces it.

## Worked around, not fixed

`method_calls_literals.spl` now defines `_sffi_enum_discriminant` locally,
delegating to the existing local `_sffi_method_hir_type_discriminant` wrapper —
the same shape the three sibling modules already use, and no new direct `rt_*`
call site. That unblocks the link; it does not make the seed reject the
unresolved name, so the next module to depend on a glob-imported private helper
will fail the same way at the same late stage.

Refs: doc/08_tracking/bug/stage2_link_undefined_cpu_probe_and_surface_symbols_2026-09-13.md

---

## 2026-11-11 addendum — lane ne10 (P3 traverse, batch ne10)

**Verdict: LIVE — keep OPEN.** The expected compile-time unresolved-name error still does not
happen; the glob-imported private name resolves permissively on the current seed.

- **Seed:** tracked `bin/simple.exe` build-commit `46fe8f6b6def` (contains
  `6d15331f91eb`, verified `git merge-base --is-ancestor`). All runs seed-smoke
  (`SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe ... --mode=interpreter --no-cache`).
- **Related but narrower fix already landed:** `6d15331f91eb` (2026-11-09)
  `fix(seed-interp): error on cross-directory call of a private fn (glob/no-import leak)` gates
  the *bare-name leak* leg — its spec
  `test/01_unit/compiler/95.interp/interpreter/private_fn_call_visibility_spec.spl` passes 3/3
  on this seed.
- **This bug's leg is NOT covered by it.** A two-module same-directory glob repro
  (`use app.ma.*` + `use app.mb.*`, both defining private `fn _helper(x: i64) -> i64`, importer
  calls `_helper(1)`) still runs, exit 0, printing the resolved result (`R=2`) — only a
  `compiler_cross_module_private_symbol_collision` warning is emitted. A single-module
  cross-directory glob repro (`use app.sub.lib.*` calling its private `_helper`) also still runs,
  exit 0. In both shapes the private name resolves through the glob import binding itself, which
  the `6d15331f91eb` call-time gate does not reject.
- **Native-lowering leg (unmangled extern at link):** not re-provable on this lane — the Windows
  native-build hang is a known live defect, never retried. Grant command:
  `SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe ./bin/simple.exe native-build --source src
  --entry build/p3ne10-probes/row7fix/app/main.spl --output build/p3ne10-probes/row7fix/app/main`
  (minimal repro entry as described above; run on a host where native-build does not hang, and
  confirm the link either resolves per-module-mangled or fails at compile time, never an
  unmangled `_sffi_*` reference).
- **The call-site workaround in this doc remains in place** (`method_calls_literals.spl` defines
  `_sffi_enum_discriminant` locally), so the original Stage-2 link is not blocked by this row
  today; the seed behavior this record is about is unchanged.
