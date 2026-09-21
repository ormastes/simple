# Native LLVM inline guarded return parses `return` as a global

Date: 2026-09-22
Status: mitigated in source; compiler diagnosis remains open

## Reproducer

`test/03_system/native/inline_guard_return_llvm.spl` contains an inline
guarded return. Build it with the admitted Stage 2 runtime using
`native-build --backend llvm --entry-closure`.

## Failure

The Phase 2 Windows LLVM build reported `llvm global load referenced
undeclared symbol 'return'` while compiling
`src/lib/nogc_sync_mut/rt_hal/process_task_arena.spl`.

The LLVM owner traced the malformed `GlobalLoad('return')` to compact
`if condition: return value` statements. The parser/HIR path must preserve
`return` as a statement token in this layout. The local source now uses the
block form in the affected arena helpers; this is a mitigation, not a claim
that the parser defect is fixed.

## Required follow-up

Fix the parser/HIR handling of an inline guarded return and run the reproducer
through the Windows LLVM Stage 2 path. Keep the source form test as a
regression guard.
