# JTAG STAGE1 IDCODE check is self-referential — a wrong DUT IDCODE cannot fail it

- **Filed:** 2026-07-28
- **Severity:** medium — one assertion inside an otherwise-gating testbench is vacuous
- **Status:** open
- **Found via:** Lane R3 gate-honesty audit

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
