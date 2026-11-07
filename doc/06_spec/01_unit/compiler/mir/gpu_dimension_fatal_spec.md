# GPU dimension and argument ownership controls

Status: AUTHORED / NOT_RUN. Manual companion, not generated execution evidence.

- A real HIR parameter used as an index dimension produces a fatal diagnostic
  with the original source span, accepted by the production driver fatal gate.
- All five index instructions preserve literal0/1/2; omitted dimension uses0.
- A call-valued dimension emits one call before the rejected recovery instruction.
- CAS and eight ordinary atomics accept bound pointer/data parameters; emitted
  instruction operands retain the original parameter-local identities.
- Effect callees are defined sequentially in the caller-owned symbol table;
  their distinct IDs and exact stored names are checked before lowering.
- Call-valued CAS pointer/expected/desired and atomic/shuffle operands emit one
  call each in left-to-right order. The final operation consumes exactly those
  result locals, after all operand calls, with no subsequent operand evaluation.

The executable spec invokes the production lower_gpu_intrinsic_call owner and
registry. It retains three-field MirInstKind.Call from the current source schema.
No GPU hardware, source-level full compilation, native device execution or
published-artifact qualification is inferred from authored MIR assertions.
Original PR7316 was closed with an unresolved P1; this repaired replacement
restricts dimension inspection to five exact names and preserves other argument
lowering paths. Runtime verification waits for an admitted compiler lane.
