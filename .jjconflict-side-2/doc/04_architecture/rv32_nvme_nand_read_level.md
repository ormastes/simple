# RV32 NVMe NAND Read-Level Architecture

The existing RV32 firmware owns policy. A reserved `.nandram` linker section
provides a fixed volatile word store; the Simple firmware is the only owner of
its layout and operations. Ordinary RV32 loads/stores reach that store through
the target memory fabric, not through a NAND MMIO register interface.

```text
NVMe lifecycle -> SQ/CQ state -> NAND RAM operations -> sense/ECC
      |              |                |                  |
 startup/admin/io  submit/complete  erase/program/read  retry/FCR/remap
      +--------------------+-----------------------+
                           |
                     UART stage log
                    /              \
       AXI4 RAM + AXI-Lite obs   BRAM capture -> JTAG USER4
```

The target-neutral pure helpers contain no MMIO or assembly. RV32-only entry
helpers call bounded runtime loads/stores for linker symbol `_nandram_start`. This
keeps host tests deterministic while GHDL and FPGA execute the same stateful
firmware path. The pre-board AXI gate remaps `.nandram` into a
wait-state-injected RAM slave and counts accesses only within its ELF-derived
range. Unknown stages, out-of-range words, overwrite attempts, and exhausted
retries fail closed.

The scalar model is the executable controller policy oracle, not an analog NAND
model. It derives ECC error counts from threshold distance, tries fixed downward
retention and upward disturb ladders, and admits refresh only after correction
and payload matching. FCR is read-correct-erase-program-verify; verification
failure retires/remaps. The full `hardware.nand_emu` backend remains responsible
for distribution, wear, and timing fidelity while presenting the same outcomes.
