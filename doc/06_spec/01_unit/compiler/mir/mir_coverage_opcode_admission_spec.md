# Typed MIR Coverage Opcode Admission

This executable unit specification freezes the first typed MIR coverage
opcode boundary. Decision and condition probes are ordered observations whose
boolean operands must survive MIR traversal and optimization until an admitted
backend lowering consumes them.

## Optimizer contract

The optimization engine treats both probe variants as live side effects and
records each observed boolean operand as a use. Operand liveness is transitive
through a cast: the cast result remains live because the probe observes it,
and the cast input remains live because it defines that result. This also
holds when a no-op cast is rewritten to `Copy` before engine DCE.

## Executable scenarios

The mirrored spec verifies:

1. decision and condition opcodes serialize with stable identity metadata;
2. the MIR visitor walks both boolean operands;
3. both opcodes are mandatory DCE observations;
4. direct definitions used only by either probe survive engine DCE;
5. cast inputs used transitively only by either probe survive no-op cast
   rewriting and engine DCE;
6. malformed IDs, paths, positions, and operand types fail closed;
7. SSA rewriting and inlining reject probe-bearing blocks;
8. the interpreter rejects unlowered probes; and
9. LLVM translation paths reject unlowered probes before emission.

## Deferred integration

This contract admits optimizer preservation only. HIR-to-MIR insertion,
runtime counter lowering, zero-count manifest publication, and target backend
emission remain separate capability-gated changes.
