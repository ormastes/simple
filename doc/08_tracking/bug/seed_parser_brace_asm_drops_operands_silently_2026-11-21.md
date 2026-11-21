# Seed parser: brace-form `asm volatile { ... }` drops operand clauses silently

- **Status:** open
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

## Fix wanted

Either lower operand clauses in the brace form (parse trailing
`in(...)`/`out(...)`/`inout(...)`/`clobber(...)` lines as constraints), or reject
a brace block that contains clause lines or `{name}` placeholders with a
diagnostic pointing at the parenthesized form. Silent pass-through is the bug.
Same fix needed in the pure-Simple parser if it shares the behaviour.
