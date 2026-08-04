# Stage 4 leak checker resolves shadowed compatibility facades

## Status

Fixed in the LLVM 23.1 Stage 4 bootstrap lane on 2026-08-04.

## Symptom

The second full Stage 4 cycle crossed the CLI handler repair, parsed all 1,351
surfaces, and failed HIR ownership in `compiler.tools.leak_check.main` for
`interpret_file` and `MemLeakEntry`.

## Root cause

`compiler.driver` resolves to the package's empty `mod.spl` before its exporting
`__init__.spl`, so it cannot provide `interpret_file` or `CompileResult`.
Likewise, `std.mem_tracker` resolves to `mem_tracker/mod.spl`: its functions are
physical there, but its private sibling-type import does not re-export
`MemLeakEntry`. Several runtime tiers independently declare that type, so an
unqualified workaround could also select the wrong terminal identity.

## Fix and regression

The leak checker imports the in-process interpreter function and compile-result
type from their physical compiler owners, and imports `MemLeakEntry` from the
exact `nogc_sync_mut` type owner used by `parse_leak_dump`. The adjacent external
runner compile-result and internal runner CLI callable use the same physical
ownership rule. A focused native contract imports the real leak-check entry so
the complete module family must lower and link.
