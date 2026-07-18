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
