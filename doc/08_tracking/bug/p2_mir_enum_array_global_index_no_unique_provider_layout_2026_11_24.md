# Phase 2 MIR ICE: indexing a `[Enum]` global demands a struct record layout

- **Status:** FIXED (2026-11-24)
- **Component:** `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`
  (LoadGlobal of an Array/Slice-typed global, `array_element_struct_syms`
  registration)
- **Found:** 2026-11-23, rb5 Stage 3 attempt
  `recovery-threads1-20261123T110416-60534` (Phase 2 self-hosted compiler,
  caught ICE, `phase=mir_lower`)

## Symptom

Compiling module `compiler.backend.linker.elf.elf_static_link` with the
self-hosted compiler fails in MIR lowering:

```
MIR lowering error: array return record element has no unique provider layout: compiler.backend.linker.reloc_engine.RelocArch
```

## Trigger

`src/compiler/70.backend/linker/elf/elf_static_link.spl` declares a
module-level global whose element is an ENUM
(`RelocArch`, `src/compiler/70.backend/linker/reloc_engine.spl:221`) and reads
it by index inside `elf_apply_worker`:

```simple
var _elf_apply_target: [RelocArch] = []
...
val arch = _elf_apply_target[0]
```

The source is valid Simple; the compiler is wrong.

## Cause

`expr_dispatch.spl:532-539` (LoadGlobal, `[Named]` element with no optional
payload struct name) registered
`self.array_element_struct_syms[dest.id] = self.struct_value_provenance_key(global_elem)`
unconditionally, i.e. for enum elements too. Indexing that local reaches
`remember_array_index_projection_provenance` (`expr_dispatch.spl:1556-1584`),
which calls `checked_array_record_layout(stable_owner)`
(`switch_operators_calls.spl:1490-1504`) BEFORE its own
`SymbolKind.Struct | SymbolKind.Class` filter. That function requires a struct
layout (`struct_field_order`, `struct_field_hir_type`, a unique
`composite_layout_owner_counts` entry) and calls `error_fatal` when an enum key
arrives.

Every sibling registration site already guards on record kinds:
`_MirLowering/function_lowering.spl:938` (`[T]` parameter),
`mir_lowering_stmts.spl:5393` (`for x in` collection), and the return-array
prescan (`module_lowering.spl:2409-2423`,
`declaration_providers_v1.spl:580-592`) registers `__no_struct_element__` for
non-struct/class elements; `expr_dispatch.spl:1306-1318` documents that enums
need no record owner. The LoadGlobal branch was the only unguarded one.

## Fix

`expr_dispatch.spl`: register `array_element_struct_syms` for the loaded global
only when `global_elem.kind` is `SymbolKind.Struct` or `SymbolKind.Class`
(`case _: ()`), matching the parameter site. No change to
`elf_static_link.spl`.

## Evidence

- rb5 Stage 3 attempt `recovery-threads1-20261123T110416-60534`, go-to-end
  summary: Phase 2 ICE on `compiler.backend.linker.elf.elf_static_link` with
  the message above.
- Spec `test/01_unit/compiler/mir/enum_array_global_index_lowering_spec.spl`
  lowers `enum Mode: A | B`, `var g: [Mode] = []`, `g = [Mode.B]; val x = g[0]`
  through `parse_full_frontend -> HirLowering -> MirLowering` and asserts zero
  lowering errors. RED on the unfixed tree (1 error containing
  "no unique provider layout"), GREEN with the fix. This asserts the lowering
  ICE is gone at MIR level; it does not execute a native binary (a native-build
  run was off limits while a Stage 3 build occupied the host).
- `test/01_unit/compiler/mir/array_field_element_shape_spec.spl` still passes
  (4/4), covering the struct/enum field-array shape path.

## Workaround (applied for the rb5 run only)

`_elf_apply_target` was made a scalar `RelocArch` global instead of a
one-element `[RelocArch]` array. Not landed; the compiler fix above removes
the need for it.
