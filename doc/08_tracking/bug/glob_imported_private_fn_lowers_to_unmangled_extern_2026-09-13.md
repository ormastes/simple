# A glob-imported PRIVATE fn lowers to an unmangled extern instead of failing to resolve

- **Status:** OPEN (2026-09-13). Worked around at the call site, NOT fixed.
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
