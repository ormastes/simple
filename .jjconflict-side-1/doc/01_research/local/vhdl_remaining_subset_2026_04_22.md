<!-- codex-research -->
# VHDL Remaining Synthesizable Subset Research

Date: 2026-04-22

## Scope

This pass researched remaining work after the CLI VHDL path, GHDL add proof, and support-matrix updates. The scope stays on the selected conservative synthesizable subset, not arbitrary Simple-to-VHDL.

## Findings

- Source facade: the pure Simple fallback still had scalar gaps versus the support matrix. Missing pieces were fixed-width `i8/i16/u16/u64` ports/results, scalar comparisons, boolean logic, literal shifts, unary negation/not, and direct CLI smoke coverage.
- Source facade boundary: unknown expressions could previously pass through as raw VHDL text. The fallback now routes only recognized scalar expressions and returns an error for unsupported expressions before falling through to the external bridge.
- Backend aggregates: MIR tuple and payloadless enum aggregates were the main tractable backend gap. Tuple aggregates now use generated record types with `fN` fields. Payloadless enum aggregates lower to variant literals. Payload-bearing enums remain deferred hard errors.
- Validation: source-facade output now has a GHDL analysis/elaboration proof. Backend computed `if` and `switch` process lowering now have GHDL-backed checks in addition to text checks.
- CLI/API tests: stale external-facade expectations were updated, and `bin/simple compile --backend=vhdl` now has direct smoke coverage for explicit `-o` and default `.vhd` output.

## Still Deferred By Design

- Dynamic allocation, pointer/address MIR, generic calls, indirect calls, arbitrary intrinsics, and unsupported terminators remain hard errors.
- Payload-bearing enum aggregates are deferred because synthesizable representation needs a tagged record contract.
- Multi-function arbitrary source-to-VHDL remains partial; the supported source fallback is intentionally single-function scalar expression oriented.
- Yosys remains optional. GHDL is the required Linux validation tool for this lane.
