<!-- codex-research -->
# Inline Assembly Matrix Research — 2026-04-21

## Search Scope

Searched asm docs, specs, compiler frontends, Rust lowering/codegen, Simple OS
sources, and boot/runtime files for `asm(...)`, `asm:`, `asm "..."`,
`asm { ... }`, `InlineAsm`, and `inline_asm`.

## Existing Test Surface

Primary asm SPipe files:

- `test/unit/compiler/native/inline_asm_spec.spl`
- `test/unit/compiler/native/inline_asm_constraints_spec.spl`
- `test/unit/compiler/native/asm_match_spec.spl`
- `test/feature/baremetal/inline_asm_integration_spec.spl`
- `test/unit/compiler/backend/riscv32_asm_spec.spl`
- `test/unit/compiler/semantics/safety_checker_spec.spl`
- `test/system/features/baremetal/unsafe_spec.spl`

Rust parser/codegen tests:

- `src/compiler_rust/parser/src/stmt_parsing/asm.rs`
- `src/compiler_rust/compiler/src/codegen/codegen_instr_tests/inline_asm.rs`

## Current Syntax Contract

Canonical raw embedded asm syntax is:

```simple
asm {
    "nop"
}

asm volatile {
    "wfi"
}
```

Still-supported compatibility forms:

- `asm: "nop"`
- `asm volatile: "nop"`
- `asm: ...indented string block...`
- `asm volatile: ...indented string block...`
- `asm(...)` for legacy operand/constraint syntax

Old `asm(...)` remains valid but should warn in the Rust parser. It is not an
error because operand constraints still depend on it.

## Execution-Mode Findings

Interpreter mode:

- Rust interpreter sees `Node::InlineAsm` and intentionally skips it.
- Pure interpreter returns `0` for `EXPR_ASM` and `EXPR_ASM_MATCH`.
- This is acceptable only for no-op smoke fixtures; hardware-effect asm must be compiler/loader-only.

Loader mode:

- Native project build clears/collects inline asm blocks and links generated `simple_asm_blocks.o`.
- Loader tests should verify preservation/linking intent, not hardware execution.

Compiler mode:

- HIR lowering preserves raw no-operand asm as `HirStmt::InlineAsm`.
- Operand-bound or target-matched asm is currently skipped in Rust HIR lowering.
- Native codegen registers raw asm blocks and emits them through generated C `__asm__ volatile`.
- LLVM-lib still rejects `InlineAsm`.

## Platform Matrix Needed

Minimum matrix: six targets times three execution modes.

Targets:

- `x86_32`
- `x86_64`
- `arm32`
- `arm64`
- `riscv32`
- `riscv64`

Modes:

- `interpreter`
- `loader`
- `compiler`

Each target has a safe raw `nop` fixture in
`test/unit/compiler/native/inline_asm_matrix_spec.spl`.

Privileged instructions such as `hlt`, `wfi`, `mret`, `iretq`, control-register
access, and port I/O belong in compiler/loader syntax-preservation tests unless
a QEMU/hardware harness executes them safely.

## Simple OS Conversion Notes

Simple OS still contains many `.c`, `.h`, `.s`, and `.S` files. The safest
conversion order is:

1. Convert small runtime stubs that are ordinary functions.
2. Convert instruction wrappers to `.spl` with `asm {}` when no operands are needed.
3. Keep boot entry assembly until Simple supports section placement, global labels, naked functions, exact ABI entry symbols, and early stack setup.
4. Keep C libc compatibility shims until native linking no longer requires the external ABI surface.

## Open Blockers

- Operand-bearing `asm {}` is not implemented.
- Operand-bound asm in Rust HIR lowering is currently skipped.
- Pure parser accepts raw braced asm strings but not structured operands.
- Existing broad SPipe tests mostly check strings, so they can mask parser/lowering/codegen gaps.
