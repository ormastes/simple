# RISC-V debug module hard-wires `dmstatus.authenticated = 1` (no auth unit exists)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

# 2026-11-05 — FIXED (work branch work/libbug-linux-rvdbg-20261105)

Root cause: `debug_registers.vhd` drove `dmstatus.authenticated` from the
literal `'1'` and no auth state existed anywhere in the tree, so the live
System Bus Access engine answered every JTAG session as authenticated.

Fix (minimal honest lifecycle, per the doc's prescription):
- `dmstatus.authenticated` is now a computed register (`authenticated_r`),
  and `dmstatus.authbusy` reflects the challenge window. No constant remains.
- New fuse/OTP-bound lifecycle inputs on `riscv_debug_module` /
  `debug_registers`: `lifecycle_i` — OPEN ("00", unprovisioned fab/test:
  no challenge), PROVISIONED ("01", default: authdata challenge vs
  `auth_key_i`), LOCKED ("10": challenge ignored, SBA denied). RMA re-entry
  stays an OTP-controller operation (fuses moved back to OPEN for the RMA
  station, then re-locked); the DM only reads the fuse snapshot.
- New `authdata` challenge register at DMI 0x30 (write-only, reads 0);
  `dmi_bus` now forwards 0x30 to the DM. Match authenticates, mismatch
  de-authenticates; authbusy sets on the write and clears on the next
  DMSTATUS read; dmactive=0 resets authentication with the rest of the DM.
- SBA gating: the single `sb_start` choke point denies every bus access
  while unauthenticated (sberror = 7 "other", no sb_re_o/sb_we_o, memory
  untouched).
- `tb_sba` authenticates via the challenge before touching the bus; the
  OpenOCD/hart e2e glue (`tb_openocd_bitbang`, `hart_core_glue`) ties OPEN
  explicitly as the documented development state.

Verification (GHDL 4.1.0 simulation, all absolute-string oracles):
- New `src/lib/hardware/debug/tb_auth_gate.vhd`: CHECK1 authenticated=0
  after activation; CHECK2 negative gate (unauthenticated SBA write denied,
  sberror=7, zero bus activity); CHECK3 wrong key rejected + authbusy
  observable; CHECK4 correct key authenticates and SBA reads memory;
  CHECK5 wrong key de-authenticates; CHECK6 dmactive=0 resets auth;
  CHECK7 LOCKED denies even the correct key; CHECK8 OPEN works without a
  challenge. Prints "AUTH GATE PASS".
- Non-vacuity (the doc's mandatory negative gate): with the challenge
  comparison sabotaged (`dmi_wdata = auth_key_i` -> always-true), the gate
  turns red at "CHECK3 FAIL"; with the SBA deny branch disabled, it turns
  red at "SBA bus access started while unauthenticated".
- Regression: tb_jtag_dtm_dmi (STAGE1), tb_debug_module (STAGE2),
  tb_abstract_cmds (STAGE3), tb_debug_csrs (STAGE4), tb_sba (STAGE5),
  tb_soc_jtag_debug, tb_hart_integration, tb_uart_bscan_log and
  tb_bscane2_bridge all still pass.
- Executable spec: `test/01_unit/lib/hardware/debug/dm_auth_gate_spec.spl`
  (5 examples, RED before the fix: hardwire still present + tb_auth_gate
  could not analyze; GREEN after, including both sabotage runs).
- Golden manifest pins regenerated for the touched files (see the
  2026-11-05 note in doc/08_tracking/hardware/golden_vhdl_manifest_2026-07-26.txt);
  tb_auth_gate.vhd pinned as a new golden.

Remaining concerns (honest scope limits):
- The 32-bit auth key is a simple equality challenge, not a nonce-based
  protocol; a provisioned device is still exposed to brute force over a
  slow DMI. A real part wants a challenge/response with an OTP-only secret
  and attempt throttling.
- `sberror = 7` for denial is implementation-defined (spec allows an error
  or an absent SBA); document the choice in the 0.13 compliance notes.
- The gdb/OpenOCD e2e scripts exercise the OPEN state only; there is no
  e2e flow that performs the authdata challenge through OpenOCD.
- Abstract commands (GPR/CSR) are intentionally not gated in this change;
  they do not reach system memory.

Tracked as gate 6.4 in `doc/03_plan/hardware/simple_riscv_production_dft_svap_plan.md`,
landing ADVISORY and honestly RED.

## 2026-11-05 — Verification (work branch work/riscv-rtl-infra-20261105)

Status: **already fixed at tip of release/1.0.0** (base c909eb427c3); the
2026-11-05 FIXED section above (from work/libbug-linux-rvdbg-20261105) is
present in this branch. Verified by source inspection:

- No constant `authenticated` remains: `debug_registers.vhd:743` drives
  `dmstatus_v(7) := authenticated_r`, a computed register reset to `'0'`
  (:386) and set only by the lifecycle/authdata logic (:395-401, :672-674).
- `lifecycle_i` fuse input exists on `riscv_debug_module.vhd` (:94) and the
  SBA deny branch (`sberror_r <= "111"` while `authenticated_r = '0'`) is at
  :332-333.
- `tb_auth_gate.vhd` and the executable spec
  `test/01_unit/lib/hardware/debug/dm_auth_gate_spec.spl` are both in-tree.

Executable evidence (Rust seed binary, aarch64 host, interpreter mode):

```
SIMPLE_RUST_SEED_WARNING=0 timeout 120 \
  /home/yoon/dev/simple/src/compiler_rust/target/bootstrap/simple test \
  test/01_unit/lib/hardware/debug/dm_auth_gate_spec.spl --mode=interpreter
```

Outcome: `outcome=OK declared>=5 executed=5 passed=5 failed=0` — **5/5
examples pass**, including the sabotage (non-vacuity) examples. Limitation:
GHDL is not installed on this host (`command -v ghdl` → not found), so the
VHDL testbench simulation itself was not re-run here; the prior GHDL 4.1.0
evidence in the FIXED section stands, and the executable spec pins the same
invariants against the current sources. No code change needed in this lane.

