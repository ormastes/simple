# RISC-V debug module hard-wires `dmstatus.authenticated = 1` (no auth unit exists)

**Date:** 2026-09-01
**Found by:** workstream F (`simple_riscv_production_dft_svap_plan.md` §2), independently re-verified by the parent session.
**Status:** OPEN. Not a shipped-product vulnerability — this is pre-silicon RTL in
a development core. It is filed now because a debug-authentication lifecycle must
exist *before* any part is built from this RTL, not after.

## Measured, verbatim

`src/lib/hardware/debug/debug_registers.vhd:661`

```vhdl
dmstatus_v(7) := '1';              -- authenticated (no auth unit)
```

Documented as intended-for-now at `:20`:
`--   0x11 DMSTATUS — version=2 (0.13), authenticated=1 (no auth), and`

A case-insensitive scan of `src/lib/hardware/debug/` for
`authdata|authbusy|authenticated` returns **exactly these two lines**. There is
no `authdata` register, no challenge/response flow, and no lifecycle state
anywhere in the tree.

## Why it matters

The debug module exposes a live System Bus Access engine
(`riscv_debug_module.vhd:9-12`, DMI `0x38..0x3D`). SBA reads and writes system
memory without involving the hart. A part manufactured from this RTL would
therefore answer *authenticated* to any JTAG connection and grant it system-bus
read/write — i.e. full memory access over the debug port, with no gate.

For an SSD controller this is the whole threat model: keys, firmware images, and
user data all sit behind that bus.

## Required fix (design, not yet implemented)

A debug/trace security lifecycle: authenticated must be a computed state, not a
constant; `authdata` challenge flow; lifecycle states (open -> provisioned ->
locked -> RMA-unlock) bound to fuses/OTP; SBA gated on the authenticated state;
and a documented, auditable path for RMA re-entry.

## Test obligation

A negative gate is mandatory and must be non-vacuous: assert that an
unauthenticated DMI session is **denied** SBA, and prove the gate can turn red by
sabotaging the auth check. A gate that only asserts the positive path would pass
against exactly the current broken code.

Tracked as gate 6.4 in `doc/03_plan/hardware/simple_riscv_production_dft_svap_plan.md`,
landing ADVISORY and honestly RED.
