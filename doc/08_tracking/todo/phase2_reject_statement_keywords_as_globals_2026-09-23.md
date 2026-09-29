# Phase2: reject statement keywords before global lowering

The admitted Stage2 compiler can lower malformed or unsupported compact suites
such as `if condition: return value` as an identifier expression, eventually
reporting an LLVM undeclared global named `return`. A similarly misplaced
instance method can let `me`/`self` decay to global lookup.

The 2026-09-23 source repair keeps affected production files within the proven
Stage2 grammar. A later compiler change should diagnose statement keywords and
ownerless instance receivers during parsing or HIR lowering, before MIR emits a
`LoadGlobal`. Keep the LLVM undeclared-symbol check fail-closed.
