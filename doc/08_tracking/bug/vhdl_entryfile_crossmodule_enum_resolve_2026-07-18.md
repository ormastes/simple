# VHDL backend / entry-file compile: imported enum type unresolved (cross-module)

- **Date:** 2026-07-18
- **Status:** open
- **Severity:** medium (blocks any multi-file RTL through the VHDL backend)
- **Area:** compiler VHDL backend + HIR entry-file pre-scan

## Symptom

```
bin/simple compile --backend=vhdl src/lib/hardware/nand_emu/rtl/pin_frontend.spl \
  -o build/vhdl/nand_emu/pin_frontend.vhd
error: VHDL compilation failed: semantic: Undefined("undefined identifier: NeLatchKind")
```

`NeLatchKind` is a payload-less enum defined in
`src/lib/hardware/nand_emu/nand_types.spl` and imported by
`rtl/pin_frontend.spl` via `use`. Locally-defined types in the entry file
(NePins, NeColCounter) resolve fine; only the imported type fails.

## Independent second symptom (same root)

`bin/simple run` on the host spec for the same file warns
`[WARN] Failed to load imported types from ["hardware","nand_emu","rtl","pin_frontend"]: Unknown type: NeLatchKind`
and JIT falls back to interpreter with `HIR lowering error: Unknown type:
NeLatchKind`. The interpreter recovers (spec passes 15/15); the VHDL backend
has no fallback and hard-errors before emission.

## Ruled out

Import-prefix form: both `use std.hardware.nand_emu.nand_types.NeLatchKind`
and bare `use hardware.nand_emu.nand_types.NeLatchKind` produce identical
errors.

## Expected

Cross-module type resolution for entry-file compilation (VHDL backend and the
HIR pre-scan) should resolve imported enums exactly as module-graph
interpretation does. Existing RTL under `src/lib/hardware/rv32i_rtl/` avoids
this by keeping shared types in a `pkg` module compiled in the same unit set —
worth checking how the soc_vhdl_gen driver assembles its unit list vs the
single-entry `compile --backend=vhdl` path.

## Workaround until fixed

None acceptable in-module: inlining the enum into pin_frontend.spl would
duplicate a type name (forbidden — interpreter global struct registry).
nand_emu RTL feasibility is otherwise proven (host spec green); VHDL emission
for multi-file RTL waits on this fix or on routing through the soc_vhdl_gen
driver.

## Fixed 2026-11-05 (RTL lane, PR #NNNN — wait verification)

**Root cause (verified at release/1.0.0 tip):** the seed-side module-graph
resolution this bug originally hit is long fixed (the seed resolves
`hardware.nand_emu.nand_types.NeLatchKind` fine; the host spec passes 15/15
with no "Unknown type" fallback warning). The live defect was in the pure-Simple
VHDL source facade, `src/compiler/80.driver/driver_compile_vhdl_source_map.spl`
(`_compile_simple_vhdl_subset`), used by `aot_vhdl_file` /
`bin/simple compile --backend=vhdl`:

1. The subset transpiler is textual and single-file: it learns enum/type
   declarations only from the entry source text, so an imported enum name
   could never resolve.
2. Independently, any leftover `use` line broke the single-function facade
   scan in `driver_compile_vhdl_codegen.spl` — the first unrecognized line is
   captured as the function `header`, yielding
   "VHDL subset fallback requires a single function declaration". So *any*
   entry file with imports failed even before alias resolution.

**Fix:** `_compile_simple_vhdl_subset` now runs a pre-pass
(`_simple_vhdl_resolve_imported_type_decls`) that parses `use` lines (both
`use a.b.Name` and `use a.b.{N1, N2}` forms), resolves modules through the
canonical `resolve_module_path`, extracts imported `enum`/`type` declarations
(handling `pub` prefixes, docstrings, and comments in real module files),
splices them ahead of the entry source, and strips the consumed `use` lines.
Imported symbols that are not types and unresolvable modules are left
untouched — unknown types still fail closed downstream exactly as before.

**Verification:** two new regression cases in
`test/03_system/compiler/vhdl_source_facade_spec.spl` (relative cross-module
import; std-lib `hardware.nand_emu.nand_types.NeLatchKind` import) — both FAIL
before the fix and PASS after. Full spec: 39 passed, 3 failed (the 3 failures
pre-exist at base: 37 passed/3 failed of 40 before this change). Adjacent
`driver_public_compile_split_contract_spec` 2/2 and nand_emu
`module_import_spec` 11/11 stay green.

**Still open (recorded, not silently normalized):** the Rust seed's own VHDL
codegen (`src/compiler_rust/.../codegen.rs`) supports no enum types at all
("VHDL backend unsupported type id ... Enum") — diagnostic-only seed path,
out of scope for this fix.
