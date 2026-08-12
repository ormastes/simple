# RISC-V Gen2 HWIR VHDL Ownership

## Purpose

This focused unit specification keeps typed Gen2 HWIR construction separate
from target-language serialization. It is a source-ownership gate, not a VHDL
simulation or qualification receipt.

## Scenarios

1. Walk every `.spl` source under `src/compiler/50.mir/hwir/`, rather than a
   hand-maintained subset. Exclude only `types.spl`, whose declarative
   vocabulary records VHDL reserved identifiers for validation, and any
   testbench-only literal path.
2. Reject unmistakable serializer constructs from every remaining source:
   VHDL preludes, `std_logic_vector`/`std_ulogic`, numeric conversion and
   edge-detection calls, architecture delimiters, and direct instantiation or
   map syntax. The guard intentionally does not reject isolated reserved words
   that valid typed HWIR can name or discuss.
3. Exercise the guard with a synthetic VHDL prelude/architecture fragment and
   show that a typed `HwSignal` description and a testbench literal do not
   create a false positive.
4. Confirm that the strict backend emitter owns the VHDL prelude.

## Requirement traceability

- NFR-G2-004 — semantic HWIR never embeds direct VHDL.

## Evidence status

The executable source is
`test/01_unit/compiler/50.mir/hwir_vhdl_ownership_spec.spl`. A bootstrap-seed
run is diagnostic only; a qualified self-hosted run is required for release
evidence.
