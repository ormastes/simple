# Seed parser: brace-form `asm volatile { ... }` drops operand clauses silently

- **Status:** fixed (2026-11-22)
- **Found:** 2026-11-21, riscv32 SimpleOS kernel link lane
  (`scripts/check/check-simpleos-riscv32-kernel-link.shs --link-only`)
- **Symptom:** the riscv32 `syscall` in `src/os/userlib/syscall_raw.spl`, written
  as `asm volatile { "mv a7, {id}" ... in(reg) id32 ... out(reg) result32 }`,
  failed LLVM codegen with `<inline asm>:1:9: unknown operand  mv a7, {id}` and
  `unexpected token  in(reg) id32`. The operand clauses reached LLVM as
  instruction text.

## Cause

`src/compiler_rust/parser/src/stmt_parsing/asm.rs` `parse_asm_braced` (`:97`)
captures the raw text between the braces, `normalize_raw_asm_instructions`
(`:253`) splits it into lines, and the node is built with `constraints: vec![]`
(`:132`). `hir/lower/stmt_lowering.rs:1843` treats empty constraints as a raw
block, so `{name}` placeholders are never rewritten and clause lines such as
`in(reg) x` / `out(reg) y` are emitted verbatim. No diagnostic is raised.

The parenthesized form (`asm volatile("...", name = in(reg) x, clobber("a0"))`)
is parsed by `parse_asm_parenthesized` (`:154`) and lowered to LLVM constraints
by `mir/lower/lowering_stmt.rs:2561`.

## Workaround (tagged)

`syscall_raw.spl` riscv32 block moved to the parenthesized form with explicit
`clobber("a0".."a4","a7","memory")`; pinned by
`test/01_unit/os/syscall_raw_rv32_asm_spec.spl`.

## Resolution (2026-11-22)

`parse_asm_braced` (`src/compiler_rust/parser/src/stmt_parsing/asm.rs`) now extracts
unquoted operand, clobber, and options clauses (`in(...)`, `out(...)`, `inout(...)`,
`lateout(...)`, `clobber(...)`, `clobber_abi(...)`, `options(...)`, and named
`name = ...` forms) into `InlineAsmStmt.constraints`, and raises a `ParseError` on
malformed operand clauses instead of passing them through as raw assembly text.
Added Rust parser unit tests in `asm.rs`.
