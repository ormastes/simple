# Global-definition mangler drops the module prefix for a module var named exactly `values`

Date: 2026-10-17 (p2_add bootstrap-sanity cycle 104)
Lane: stage2 native codegen / symbol mangling

## Symptom

Linking any closure that references, from another compiled unit, a module-level
`var values` in `lib.nogc_sync_mut.rt_hal.boundary` fails with:

```
mold: error: undefined symbol: lib__nogc_sync_mut__rt_hal__boundary__values
```

## Evidence

Object inspection (`nm`) of the compiled unit
(`native-objects-*/mod_1248.o`, module `lib.nogc_sync_mut.rt_hal.boundary`):

- Every module global carries the module prefix:
  `lib__nogc_sync_mut__rt_hal__boundary__trace0/flags/heads/tails/statuses/...`
- The global declared as `var values: [i64]` emitted as an **unqualified local
  symbol** `B values` — the only unprefixed global in the unit.
- A referencing unit (`mod_436.o`, `compiler.mir._MirLowering.module_lowering`,
  via a cross-unit inlined boundary body) emits the undefined reference with
  the full mangled name.

Definition-site mangling and reference-site mangling disagree for this one
identifier; every sibling global (including common words like `flags`, `heads`,
`operations`) mangles correctly, so the defect is specific to the exact name
`values` at module-global-definition emission.

## Workaround landed (cycle 104)

`src/lib/nogc_sync_mut/rt_hal/boundary.spl`: module global renamed
`values` -> `boundary_receipt_values` (file-private; 4 uses). Link closure
clears.

## Required compiler fix

Find the global-definition emission path that special-cases (or fails to
mangle) the identifier `values` — likely a reserved-name/builtin collision in
the LLVM symbol emission or the module-global mangler — and remove the special
case so definition and reference mangling agree for all identifiers. Revert the
boundary.spl rename as the regression test once fixed.
