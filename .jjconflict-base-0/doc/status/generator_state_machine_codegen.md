# Feature 101: Generator State Machine Codegen

**Importance:** 4/5  
**Difficulty:** 5/5  
**Status:** COMPLETE

## Goal
Lower generator bodies into stackless state machines that preserve locals across `yield`, resume correctly, and interoperate with runtime `rt_generator_*` APIs.

## Current State
- MIR transform now discovers all `Yield` instructions, assigns monotonic state ids, and splits blocks into yield + resume blocks. It records live-after-yield vregs and resume targets in `GeneratorLowering`.
- Dispatcher and completion blocks are synthesized in MIR so codegen can switch on state later.
- Unit test (`mir::generator::tests::splits_blocks_and_collects_states`) covers multi-yield bodies and verifies block splitting + state ordering.
- Codegen expansion now lowers outlined generator bodies via `lower_generator` so dispatcher-ready MIR is what Cranelift/JIT see. Cranelift/JIT emit generator dispatchers that load ctx from runtime, branch on state, save live locals into frame slots, set next state, and return the yielded value. Runtime now holds stateful generators (`rt_generator_*` helpers for state/slots/ctx) and `rt_generator_next` calls the compiled dispatcher.
- Runtime test `generator_state_machine_runs_dispatcher` exercises the compiled dispatcher path via runtime APIs.

## Gaps
- ~~System/integration coverage for generators is still pending (current coverage is MIR + runtime unit).~~ **DONE**
- Frame slots currently store `RuntimeValue` slices; no drop accounting/GC-root validation between yields.
- ~~No interpreter/compiled parity assertions for nested control flow or captured-mutation across yields.~~ **DONE**

## Completed System Tests (runner_tests.rs)
- `runner_generator_single_yield` - basic single yield
- `runner_generator_multiple_yields` - multiple yields with sum
- `runner_generator_exhaustion_returns_nil` - exhausted generator returns nil
- `runner_generator_state_preserved_across_yields` - state across yields
- `runner_generator_with_captured_variable` - captured variable access
- `runner_generator_arithmetic_in_yield` - arithmetic expression in yield
- `runner_generator_nested_iteration` - nested iteration pattern
- `parity_generator_basic_sequence` - interpreter/codegen parity test
- `parity_generator_single_value` - interpreter/codegen parity test

## Next Steps
1) ~~Add compiled tests covering multiple yields, exhaustion, and resumed locals/captures.~~ **DONE**
2) Validate GC-safety/drops across yields; consider marking frame slots as roots.
3) ~~Wire interpreter/codegen parity tests and watch for missing await-in-generator guards.~~ **DONE** 

## Breakdown (difficulty-5)
1) **Yield-point discovery + state indexing**  
   - Walk generator body to find all `Yield` instructions.  
   - Assign each yield a state id; collect live vregs at each yield for save/restore.

2) **Frame layout + ctx ABI**  
   - Define generator frame fields: `state`, `done`, `last_value`, per-yield live slots.  
   - Decide storage: runtime struct or ctx array (consistent with runtime `rt_generator_*` ABI).

3) **MIR transform**  
   - Rewrite body: insert dispatcher block that switches on `state` and jumps into resume blocks.  
   - Replace `Yield` with: store live-ins → set next state → store yielded value → return.  
   - After final return, set `done` and return NIL.

4) **Codegen support**  
   - Emit frame alloc/init, loads/stores for frame fields, dispatcher jump table/switch.  
   - Ensure `rt_generator_next` advances state and respects `done`.

5) **Tests**  
   - Compiled generators with multiple yields, control flow, and captured locals; assert sequence of `next` calls and local preservation. 
