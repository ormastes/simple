# Mono specialization symbol id collides with a non-function symbol

Status: open. Found while proving the fn-typed parameter ABI (commit
"keep fn-type annotation shapes so generic visitors monomorphize").

## Symptom

For

```simple
fn walk<C>(n: i64, ctx: C, f: fn(i64, C) -> C) -> C: ...
fn add(n: i64, c: i64) -> i64: c + n
fn main() -> i64: walk<i64>(3, 0, add)
```

monomorphization creates one specialization, HIR names it `walk$i64`, and
MIR names it `walker_abi.C`. LLVM IR then defines `@walker_abi.C` and the
recursive call and the `main` call both target `@walker_abi.C`. The program
is still internally consistent (it links and runs), but the symbol name is
wrong. Two specializations that land on aliasing ids, or one whose alias
is another function, would break the link or call the wrong code.

## Cause

`src/compiler/40.mono/monomorphize_integration.spl`:

- lines ~255-259 set `next_symbol` to (largest **function** symbol id) + 1;
- lines ~381-387 hand that id to the specialization (`SymbolId.new(sym)`).

The module `SymbolTable` also holds non-function symbols (here the type
parameter `C`), and those can have higher ids. MIR names a function through
`provider_callable_symbol_name(fn_.symbol, ...)`
(`50.mir/_MirLowering/function_lowering.spl:404`), which resolves the id in
the symbol table and so finds `C`.

## Fix direction

Allocate specialization ids past the symbol table's maximum id (or register
the specialization in the table) instead of past the largest function id.

## Evidence

`test/01_unit/compiler/backend/generic_walker_fn_param_abi_spec.spl` finds
the walker by arity instead of name for this reason. A debug driver over
the same source printed `hir fn key=... name=walk$i64` and
`fn walker_abi.C params=[i64, i64, funcptr/2]`.
