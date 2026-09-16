# Seed native backend silently ignores `@export("C", name:)` and `@extern("runtime", ...)`

**Filed** 2026-09-01 · **Status** OPEN · **Severity** high (silent, link-time only)

## Symptom
`@export("C", name: "rt_x")` on a Simple function emits **no C alias at all**, and
`@extern("runtime", "rt_x")` emits the **Simple** name as the undefined reference
instead of the C name. Both fail silently: no diagnostic, no warning.

## Evidence (measured, not inferred)
`src/os/kernel/arch/riscv64/noalloc_pmm_runtime.spl` carries ten
`@export("C", name: "rt_riscv_*")` annotations. In the object the seed produced
for that module:

    nm mod_4.o | grep rt_riscv    ->    (no output)

Every function is present only under its mangled Simple name
(`os__kernel__arch__riscv64__noalloc_pmm_runtime__rv64_noalloc_allocate_page`).
Separately, `@extern("runtime", "rt_riscv_uart_put") fn _riscv_uart_put_raw`
produced `U _riscv_uart_put_raw`, not `U rt_riscv_uart_put`.

## Why it stayed invisible
Both are Simple<->C bridge declarations. Nothing checks that an `@export`
actually produced its symbol, so the failure only appears as an undefined symbol
at link, attributed to whatever C file used the name. In the riscv64 WM lane it
looked like "the C runtime is missing a function".

## Root cause (located, not fixed)
`src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs:204` decides
whether a function keeps its ABI name with `attr == "export" || attr == "global"`
-- an exact match on a bare attribute string. HIR lowering flattens attributes
to strings (`src/compiler_rust/compiler/src/hir/lower/module_lowering/function.rs`,
see the `section=NAME` convention), and the parameterised `export("C", name: ...)`
form never becomes the bare `"export"`, so the branch is never taken and the
`name:` argument is never read at all.

## Fix sketch
Follow the existing `section=NAME` convention: have HIR lowering emit
`export_c_name=<name>` for `@export("C", name: ...)`, and have `mangle.rs` use
that as the emitted symbol. Same for the `@extern("runtime", <name>)` call-site
name. Add a guard asserting an `@export("C")` symbol is present in the object.

## Workaround in use (2026-09-01)
`noalloc_pmm_runtime.spl` now uses forms proven to work in the same link: a plain
`extern fn rt_riscv_uart_put`, and a `spl_`-prefixed `spl_riscv_noalloc_alloc_page`
(mangle.rs keeps the ABI name for any `spl_`-prefixed function). This is a
workaround recorded per `.claude/rules/code-style.md`, not a fix.
