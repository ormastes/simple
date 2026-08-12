# HWIR Optimizer Pass Contracts

**Requirement:** REQ-G2-001  
**Source:** `test/01_unit/compiler/60.mir_opt/hwir_opt_spec.spl`

## Scope

This unit specification checks deterministic optimizer planning and accounting
over a minimal typed HWIR fixture. It is source-level evidence only: it does
not claim emitted VHDL, synthesis QoR, or target execution.

## Operator workflow

Run the mirrored executable specification with an admitted Simple runtime. Each
scenario creates the same typed module fixture, invokes a single optimizer
contract, and checks concrete result fields with built-in matchers.

## Scenarios

1. **Pass profiles.** The `speed` profile enables every modeled pass, while the
   `area` profile disables them deterministically.
2. **Width narrowing.** An eight-bit unsigned range whose maximum is seven
   reports four removable bits.
3. **Structural simplification.** Constant folds, dead state, mux reduction,
   and CSE accounting produce the expected removed-node total.
4. **Resource binding.** The area profile selects a shared multiplier binding
   with an explicitly estimated—not committed—latency contract.
5. **FSM optimization.** A speed-oriented eight-state FSM selects one-hot
   encoding and reports unreachable-state removal.
6. **Memory inference.** A two-read-port, one-write-port register-file pattern
   lowers to the true-dual-port RAM template.
7. **DSP inference.** A sixteen-bit multiply-accumulate pattern is DSP-eligible
   and updates post-pass DSP accounting.

## Evidence and limitations

The specification has eight active scenarios and no intentional skips. It
does not establish arithmetic equivalence, retiming correctness, VHDL legality,
GHDL analysis, or device-specific PPA. Those claims require the strict HWIR
emitter, target flow, and qualification receipt defined by the Gen2 plan.
