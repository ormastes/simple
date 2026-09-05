# Typed MIR Coverage Opcode Admission

This executable unit specification freezes the first typed MIR coverage
opcode boundary. Decision and condition probes are ordered observations whose
boolean operands must survive MIR traversal and optimization until an admitted
backend lowering consumes them.

## Optimizer contract

The optimization engine treats both probe variants as live side effects and
records each observed boolean operand as a use. Cast and Bitcast analysis also
records their input uses. A no-op Cast with an inline constant remains a Cast
because it has no source local; optimization must never fabricate `LocalId(0)`
for it.

The compatibility engine's local DCE is fail-safe disabled because its legacy
use collector is not exhaustive across MIR instruction kinds or terminators.
The dedicated MIR DCE owns removal. Until exhaustive collection is integrated,
the compatibility engine preserves all optimized instructions.

## Executable scenarios

The mirrored spec verifies:

1. decision and condition opcodes serialize with stable identity metadata;
2. the MIR visitor walks both boolean operands;
3. both opcodes are mandatory DCE observations;
4. direct definitions used only by either probe survive compatibility
   optimization;
5. cast inputs used transitively only by either probe survive no-op cast
   rewriting;
6. Bitcast inputs used only through a probe remain intact;
7. an inline-constant no-op Cast never becomes a Copy from fabricated local
   zero;
8. a producer consumed only by a block terminator remains intact;
9. malformed IDs, paths, positions, and operand types fail closed;
10. SSA rewriting and inlining reject probe-bearing blocks;
11. the interpreter rejects unlowered probes; and
12. LLVM translation paths reject unlowered probes before emission.

## Deferred integration

This contract admits optimizer preservation only. HIR-to-MIR insertion,
runtime counter lowering, zero-count manifest publication, and target backend
emission remain separate capability-gated changes.
