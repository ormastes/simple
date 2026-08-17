# JTAG STAGE1 IDCODE check is self-referential — a wrong DUT IDCODE cannot fail it

- **Filed:** 2026-07-28
- **Severity:** medium — one assertion inside an otherwise-gating testbench is vacuous
- **Status:** FIXED 2026-08-17 (reproduced, fixed, and re-proven under GHDL)
- **Found via:** Lane R3 gate-honesty audit

## Resolution (2026-08-17)

Confirmed LIVE by content, then fixed. The defect was a **family of 3**, not one
testbench: `tb_jtag_dtm_dmi.vhd`, `tb_soc_jtag_debug.vhd` and
`tb_bscane2_bridge.vhd` all drove their DUT with
`generic map (IDCODE_VALUE => EXPECTED_IDCODE)` and then asserted against the
same constant. (`tb_openocd_bitbang.vhd` carries the same override but has no
IDCODE assertion, so it is not vacuous; left unchanged and noted here.)

**Fix:** delete the generic-map override so each DUT uses its own default
(`jtag_tap.vhd:32` and `jtag_debug_chain.vhd:34`, both already `x"15350067"`).
`EXPECTED_IDCODE` therefore becomes an independent, spec-mandated literal, and
the change is semantics-preserving for a correct DUT.

**Reproduction (GHDL, real simulation), DUT default mutated to `x"DEADBEEF"`:**

| tree | mutant DUT | observed |
|---|---|---|
| before fix | `x"DEADBEEF"` | `CHECK2 PASS: IDCODE = 0x15350067` / `JTAG STAGE1 PASS`, rc=0 — **vacuous** |
| after fix | `x"DEADBEEF"` | `CHECK2 FAIL: IDCODE mismatch, got DEADBEEF` / `ghdl:error: assertion failed`, rc=1 |
| after fix | pristine `x"15350067"` | `CHECK2 PASS` / `JTAG STAGE1 PASS`, rc=0 — no false positive |

Verified against the repo files in the gate's own analysis order
(`scripts/check/check-riscv-hardware-gates.shs` `JTAG_UNITS`): the real
`tb_jtag_dtm_dmi` still reports `JTAG STAGE1 PASS`, so the gate stays green.

**Specs:**
- reproducing: `test/01_unit/lib/hardware/debug/jtag_idcode_gate_not_self_referential_spec.spl`
- class detection: `test/01_unit/lib/hardware/debug/testbench_self_referential_generic_class_spec.spl`
  — scans every `tb_*.vhd` under `src/lib/hardware` for *any* constant that is
  both asserted on and passed to a DUT as a generic. Proven non-vacuous:
  10 files scanned, 0 offenders after the fix; reintroducing the line in
  `tb_jtag_dtm_dmi.vhd` makes it report
  `offenders: tb_jtag_dtm_dmi.vhd:EXPECTED_IDCODE`.

Caveat: `tb_soc_jtag_debug` and `tb_bscane2_bridge` could **not** be elaborated
on this host (their chains need `hart_core_glue` / `bscane2_stub`, absent from
the directory), so their edits are content-verified but **not execution-verified**.

## Symptom

`tb_jtag_dtm_dmi` (gate "jtag tb_jtag_dtm_dmi", marker `JTAG STAGE1 PASS`)
declares its own expected IDCODE and then **configures the DUT with it**:

```vhdl
-- src/lib/hardware/debug/tb_jtag_dtm_dmi.vhd
constant EXPECTED_IDCODE : std_logic_vector(31 downto 0) := x"15350067";
...
generic map (IDCODE_VALUE => EXPECTED_IDCODE)
...
assert dout32 = EXPECTED_IDCODE report "CHECK2 FAIL: IDCODE mismatch ..."
```

`jtag_tap.vhd` declares `IDCODE_VALUE` as a generic whose default is
`x"15350067"`. Because the testbench overrides that generic with its own
constant, CHECK2 compares the DUT's output against a value the testbench itself
supplied. It exercises the IR/DR shift path (useful) but can never detect a
wrong IDCODE in the design.

## Injection evidence

| Injected defect | Observed |
|---|---|
| `jtag_tap.vhd` entity default `IDCODE_VALUE` `x"15350067"` -> `x"15350068"` | exit 0, `JTAG STAGE1 PASS` still printed — **undetected** |
| `jtag_tap.vhd` `INSN_IDCODE` `"00001"` -> `"00011"` (real decode defect) | exit 1, marker absent — correctly gates |

The second row is why this is filed as a scoped vacuity and not a fail-open
gate: the testbench does gate on genuine TAP defects. Only the IDCODE *value*
assertion is tautological.

## Suggested fix

Either drop the `generic map` override so the testbench validates the design's
own default, or add a separate assertion that the design default equals the
documented silicon IDCODE. Any board/silicon claim resting on "IDCODE verified"
should cite the second form, not CHECK2 as written.
