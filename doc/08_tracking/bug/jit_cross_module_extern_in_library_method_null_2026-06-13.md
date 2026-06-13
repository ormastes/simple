# JIT: runtime extern referenced only inside an imported library's method body links NULL (segfault)

- **Date:** 2026-06-13
- **Severity:** P1 (default-mode crash — JIT is the default execution path; any imported library that wraps a runtime extern in a class/static method core-dumps when used)
- **Status:** Open
- **Area:** codegen / cranelift JIT cross-module symbol binding

## Symptom

A `.spl` class whose method body is the *only* reference to a runtime extern
(`rt_*`) segfaults (exit 139) when the class lives in an **imported library**
module and is called from a different module — but **only in JIT/default mode**.
Interpreter mode (`SIMPLE_EXECUTION_MODE=interpreter`) works correctly.

Reproduced with the new `RtStringBuilder` wrapper in `src/lib/common/string_builder.spl`:

```
use std.common.string_builder
fn main():
    val b = RtStringBuilder.new()   # internally calls rt_string_builder_new()
    b.push("hi")
    print(b.finish())
```
- Interpreter: prints correctly, exit 0.
- JIT/default: **SIGSEGV (exit 139)**, no `[CODEGEN-WARN]` emitted.

## Discriminator (narrows the root cause precisely)

- Calling the externs **directly** from `main` (`rt_string_builder_new()` etc.)
  works in JIT — so the symbols ARE registered and resolvable by the JIT
  (`elf_utils.rs` SYMBOLS, `codegen/runtime_sffi.rs` RuntimeFuncSpec, and
  `common/src/runtime_symbols.rs` RUNTIME_SYMBOL_NAMES all include them).
- A library static method returning a constant struct works in JIT.
- A library static method that calls an extern **already referenced elsewhere
  in the compilation unit** (e.g. `rt_get_argc`) works in JIT.
- Only an extern referenced **solely inside the imported-library method body**
  NULL-jumps: `mov rdi,[rip+off]; call rdi` through a GOT slot that finalizes
  to `0`.

## Suspected root cause

The cross-module raw-name import path in
`src/compiler_rust/compiler/src/codegen/instr/calls.rs` (~line 3183) declares
the callee with `Linkage::Import` and inserts it into `ctx.func_ids`, but the
extern's name never enters the compilation unit's `referenced_names` set
(`referenced_call_names(&functions)`, `codegen/common_backend.rs:1413`). As a
result the JIT symbol-binding pass that walks `referenced_names` to bind
imported symbol addresses skips it, leaving the relocation/GOT slot at 0. The
existing NIL fallback in `calls.rs` (returns `3` + `[CODEGEN-WARN]`) is NOT
reached, so the bad import is declared "successfully" yet binds to NULL.

This is the JIT-unresolvable-extern family (cf. the InterpCall-bridge work in
`b7e9d3107ba` / `d176f2e8a30` that unboxed `rt_*` bridge results), but for the
cross-module-library case the symbol is resolvable globally and the gap is
purely that it is not enrolled into this unit's referenced-name binding set.

## Proposed fix (hypothesis — verify against codegen source)

When `calls.rs` declares a cross-module callee as `Linkage::Import`, also add
its resolved name to the unit's `referenced_names`/symbol-binding set so the
JIT address-binding pass binds it. Equivalently: have `referenced_call_names`
recurse into imported-library function bodies so externs referenced only there
are discovered. Either way, add a JIT regression test that imports a library
class wrapping an `rt_*` extern and asserts a correct (non-NULL) result.

## Impact / workaround

- Until fixed, library classes wrapping runtime externs are **interpreter-only**;
  in JIT they crash. Call the externs directly (same module as `main`), or run
  the affected program under `SIMPLE_EXECUTION_MODE=interpreter`.
- Blocks JIT/native use of `RtStringBuilder` — see
  `rt_string_concat_quadratic_2026-06-12.md` (the MCP JSON perf consumer needs
  the JIT path).

## Cross-references

- `doc/08_tracking/bug/rt_string_concat_quadratic_2026-06-12.md` (H1 primitive
  that surfaced this; interpreter-verified, JIT-blocked here)
- `codegen/instr/calls.rs` cross-module raw-name import path (~3183)
- `codegen/common_backend.rs:1413` `referenced_call_names`
