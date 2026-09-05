<!-- codex-design -->
# System Test Plan — RISC-V Gen2 Iterative M/Zmmul Owner

## Evidence target

Executable spec location:
`test/03_system/app/hardware/feature/riscv_gen2_muldiv_owner_spec.spl`.
Generated manual location:
`doc/06_spec/03_system/app/hardware/feature/riscv_gen2_muldiv_owner_spec.md`.

The spec must use the self-hosted Simple runtime, emit strict VHDL-2008, run
GHDL when available, and fail rather than count a host-only evaluator as RTL
evidence. A separate explicitly reported environment skip is permitted only
for local development; it cannot produce a qualification PASS.

Shared scenario helpers must be named before implementation:

- `step("Construct the frozen iterative owner")`
- `step("Emit strict typed HWIR as VHDL-2008")`
- `step("Drive one accepted operation through its exact iteration count")`
- `step("Hold completion under downstream backpressure")`
- `step("Compare the registered result with the independent oracle")`
- setup: `emit_muldiv_owner_fixture`, `analyze_muldiv_owner_fixture`
- checkers: `check_acceptance`, `check_stable_completion`,
  `check_architectural_result`, `check_sticky_protocol_fault`

Until a checker has a real VHDL/GHDL oracle it must call `fail(...)`; no
`pass_todo`, unconditional truth, or empty scenario is allowed. Use only
canonical SPipe matchers.

## Requirement-to-scenario matrix

| Requirement | Required executable evidence |
|---|---|
| REQ-G2-012 | Completion/v1 shape, atomic accept, sole retirement integration, held payload |
| REQ-G2-013 | Four multiply modes, four div/rem modes, Zmmul rejection, all corners and W rules |
| NFR-G2-003 | Separate RV32/RV64 VHDL contains only concrete selected widths |
| NFR-G2-011 | Synchronous reset, explicit registers, stable stalled payload |
| NFR-G2-013 | Forged identity and impossible-state fault tests, graph substitution rejection |
| NFR-G2-014 | Host-independent arithmetic vectors, 128-bit RV64 product path, deterministic hash |

## VHDL testbench protocol

Each generated entity is analyzed with `ghdl -a --std=08`, then paired with a
generated VHDL testbench and elaborated/run with `ghdl -e/-r --std=08
--assert-level=error`. Testbench operands and expected results are literals
written by the Simple spec; expected values must come from an independent
test-side reference implementation, not `evaluate_riscv_scalar_muldiv` and not
signals copied from the DUT.

At each rising edge the testbench counts accepted dispatches and accepted
completions. Assertions require completions never exceed dispatches, never
duplicate an event ID, and preserve event/decode identity. A watchdog is
`W+6` cycles for normal operations and 6 cycles for divide corners. Every
testbench asserts reset for two rising edges and checks all valid/effect/fault
outputs are zero before release.

## Directed arithmetic matrix

Run every applicable encoding with `rd=x1`, nonzero rs indices, and both X
widths where applicable:

1. RV32: MUL, MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU.
2. RV64 full-width: the same eight operations.
3. RV64 W: MULW, DIVW, DIVUW, REMW, REMUW.
4. Zmmul RV32/RV64: four multiply operations accepted; every division and
   remainder projection/owner construction rejected with the stable scope or
   provider diagnostic and no VHDL artifact.

For each multiply mode include zero, one, all ones, high bit only, maximum
positive, minimum signed, mixed-sign, and a carry-rich alternating-bit pair.
Mandatory high-half witnesses include:

- MULH: `min_signed * -1`, `-2 * 3`, and `max_signed * max_signed`;
- MULHSU: negative signed lhs times unsigned all-ones rhs;
- MULHU: unsigned all-ones times unsigned all-ones;
- MUL/MULW: overflow discarded, with MULW bit 31 both zero and one.

For each divide/remainder mode include divisor larger/equal/smaller, exact and
non-exact division, zero dividend, high-bit unsigned operands, all sign
quadrants, and remainder-sign witnesses. Mandatory corners at W=32 and W=64:

- divisor zero: quotient all ones, remainder original dividend;
- signed minimum divided by -1: quotient minimum, remainder zero;
- signed minimum divided by 1 and remainder with negative dividend;
- W forms whose 32-bit results have bit 31 set, proving sign extension for
  DIVUW and REMUW as well as signed W operations.

Each directed vector asserts the exact first-valid cycle: W+1 registered edges
after accept for normal arithmetic and 1 finalization edge for divide corners.
It also asserts no earlier completion pulse.

## Deterministic randomized differential test

For each operation/width, run at least 256 vectors from a fixed documented
64-bit seed. Bias generation toward 0, 1, -1, signed minima/maxima, powers of
two, and all-ones, then fill remaining vectors uniformly. The independent
oracle uses limb arithmetic so RV64 MULH/MULHSU/MULHU never depend on host
signed overflow or a 64-bit-only product. Division oracle explicitly implements
RISC-V zero/overflow rules before host division. On failure print operation,
W, operands, expected, actual, event ID, and cycle; never print unrelated
environment state.

## Handshake and state scenarios

1. Keep `completion_ready=0` for 7 cycles after valid. Assert valid, event IDs,
   all metadata, rd_write, and rd_value remain stable. Then accept once and
   assert valid clears on the next observed cycle.
2. Keep a second legal `dispatch_valid` asserted while busy and while result is
   stalled. Assert `dispatch_ready=0`, no fault, no operand/state corruption,
   then accept it only after the first completion has been consumed and the
   owner returns idle.
3. Hold `completion_ready=1` before and throughout execution. Assert exactly
   one completion acceptance and no combinational/fall-through completion.
4. Toggle every dispatch input after the accept edge. Assert the captured
   operation and completion payload are unchanged.
5. Use `rd=x0`; assert result arithmetic is still correct internally/at the
   normalized value boundary but `rd_write=0` and no alternate effect appears.
6. Assert reset during iteration and during a stalled completion in separate
   cases. At the reset edge all ownership, valid, payload, and fault state is
   cleared; no pre-reset event may later complete.

## Identity, fault, and fail-closed scenarios

From idle, independently forge canonical instruction, rd, rs1, rs2, instruction
length, `dispatch_lineage_valid`, illegal bit, and event/decode equality. Each
offer must leave `dispatch_ready` combinationally high for the channel but must
not capture arithmetic; at the edge it sets `protocol_fault`, after which ready,
completion valid, rd_write, traps, redirect, and memory masks stay zero until
reset. Verify one mismatch at a time so every predicate is falsifiable.

Unit-level structural tests (referenced by this system plan) mutate operation,
W/WORD agreement, provider, profile, projection SHA, completion SHA, rule order,
register width, output guard, and child graph. Each must return its stable
`HWIR-E-*` diagnostic and emit no partial VHDL. Inject each defined impossible
runtime-state predicate through a test-only initial-state fixture and require
the same sticky suppression behavior; production ports must not expose state
injection.

Divide-by-zero and signed overflow are explicitly asserted not to set fault or
trap. Backpressured valid and early ready are explicitly asserted not to fault.

## Structural and provenance scenarios

1. Construct the same owner twice and require identical canonical text,
   structural SHA-256, VHDL bytes, node comments, and manifest graph hash.
2. Change one operand width, operation, instruction, or ordered guard and
   require a different hash.
3. Inspect emitted RV32 VHDL for 32/64-bit arithmetic registers and absence of
   128-bit/runtime-XLEN selection; inspect RV64 multiply VHDL for the required
   128-bit accumulator and absence of runtime provider selection.
4. Require provenance to contain projection SHA, completion SHA, algorithm,
   W, X, and frozen operation. Require no legacy catalog/source route and no
   raw semantic VHDL owned outside the emitter.
5. Synthesize representative RV32 MUL, RV64 MULH, RV32 DIV, and RV64 DIVU
   owners with the available synthesis gate to catch unsynthesizable width or
   shift constructs. Synthesis absence is a qualification blocker, not a pass.

## Completion-composition scenario

Connect the owner through the frozen scalar-completion/v1 boundary to the
existing single architectural retirement owner. Drive ALU/control/LSU inputs
inactive, complete one multiply and one divide, and require exactly one ordered
retirement per accepted event. Aggregate `protocol_fault` into the product
fault output and demonstrate a forged mul/div request cannot retire. This test
must not introduce a mul/div-private register-file write or retirement path.

## Manual and qualification gates

Generate the mirrored manual with `spipe-docgen --no-index`; primary flow must
show construction, strict emission, accepted operation, iteration, stalled
completion, and oracle comparison without exposing setup mechanics. Run
`sspec-maintain scan` and require zero stubs and no blocker finding.

Qualification additionally requires critical policy, current self-hosted
compiler identity, GHDL and synthesis tool versions, branch coverage of at
least 80% for changed owner/HWIR modules, zero executable specs under
`doc/06_spec`, and a receipt that records all vector counts and exclusions.
Host evaluator tests, bootstrap-seed runs, or unavailable RTL tools cannot be
reported as production PASS.

## Implemented development evidence

`test/02_integration/compiler/riscv_scalar_muldiv_cycle_ghdl_spec.spl` now
generates RV32 MUL and DIV owners, analyzes and elaborates their VHDL, then
clocks reset, dispatch, W iterations, finalize, held completion, and one-time
consume. It checks exact results and absence of protocol fault. The scenario is
present but is not a qualification receipt until run by an admitted self-hosted
compiler.
