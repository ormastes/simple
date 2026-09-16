# MIR-to-LLVM bootstrap debug changes translation semantics

## Symptom

Setting `SIMPLE_BOOTSTRAP_DEBUG=1` does more than enable diagnostics. In
`MirToLlvm.translate_module` it selects the bootstrap-global function registry,
changes function emission, and suppresses TBAA. On the SimpleOS filesystem
compiler this path faults in `bootstrap_mir_function_count+0x18` because that
registry is not initialized for the normal module translation path.

## Required fix

Separate diagnostic output from translation mode. A debug flag must not change
function sources, emitted bodies, or metadata. Keep any deliberate bootstrap
translation mode behind a separately named, explicit mode flag.

## Regression gate

Translate the same MIR module with diagnostics off and on. Require identical
LLVM IR after removing diagnostic output, and require the same function count
and body sources in both runs.
