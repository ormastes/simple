# Module flattening does not mangle duplicate free-function names, so codegen cannot tell two `main`s apart

**Status:** OPEN — root-caused 2026-08-10 with a measured reproducer.
**Filed:** 2026-08-10
**Parent:** `doc/08_tracking/bug/aliased_use_import_does_not_bind_in_transitive_module_2026-08-10.md`
(this is the sub-case that fix deliberately left RED).

## Defect

`pipeline/module_loader.rs` merges every imported module's items into one
flattened `Module`. It **never renames**: two modules that both define a free
function `main` are both pushed as `Node::Function { name: "main" }`
(`module_loader.rs:672`, and the bulk `items.extend(...)` at 2195/2253/2303/2360).

The only disambiguator carried is the synthetic attribute
`__simple_flatten_module_owner__=<path>` attached by `tag_function_module_owner`
(`interpreter_state.rs:63,102-112`). Every reader of that attribute is in the
interpreter (`interpreter_eval.rs:519`, `interpreter_call/core/function_exec.rs`,
`interpreter_module/...`, `module_cache.rs`, `module_loader.rs:1441`).
**Nothing under `hir/` or `codegen/` consumes it.**

HIR lowering is consequently last-wins on the bare name
(`hir/lower/module_lowering/module_pass.rs:390-393`):

```rust
Node::Function(f) => {
    let ret_ty = self.resolve_type_opt(&f.return_type)?;
    self.globals.insert(f.name.clone(), ret_ty);
```

while BOTH bodies are still pushed unmangled into `self.module.functions`
(`module_pass.rs:1428-1431`, `:1850-1853`). Two HIR functions named `main`, no
error, no mangling.

## Measured reproducer

```
target.spl:  pub fn main(argc: i32, argv: i64) -> i32:  return argc + 41
mid.spl:     use target.{main as baremetal_main}
             pub fn cstart_init(n: i32) -> i32: return baremetal_main(n, 0)
entry.spl:   use mid.{cstart_init}
             fn main(): print("R:" + cstart_init(1).to_text())
```

| lane | result |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpreter` | `R:42` — correct |
| codegen, resolving the alias to the bare name `main` | `thread 'simple-main' has overflowed its stack / fatal runtime error: stack overflow` |

The alias bound the ENTRY module's `main`, so `cstart_init` recursed into the
program entry point. Silently wrong code.

## Why it is currently masked, not fixed

The parent fix refuses to rewrite an alias when the source name is `main`, or
when the source name has more than one definition in the flattened unit. Those
aliases stay unresolved and keep the honest hard error:

```
error: Cranelift JIT compile: SIMPLE_JIT_STRICT: unresolved external symbol
       'baremetal_main' would NULL-jump in JIT; refusing to fall back
```

That is a deliberate choice — an error beats miscompilation — but it means the
six highest-priority victims are still dead in the codegen lane:

- `src/os/kernel/arch/{x86_64,aarch64,riscv64,...}/cstart.spl:5`
  `use os.runtime.baremetal.runtime_minimal.{main as baremetal_main, __spl_exit}`

These units are compiled AOT for baremetal targets, where **no interpreter
fallback exists**, so this is the hard-`E1002` regime.

## Fix shape

Give the flattened lane owner-unique symbol names, one of:

1. Mangle duplicated free-function names at flatten time with their owner path
   (the native-project lane already has exactly this: `all_mangled` /
   `qualified_import_functions`, `pipeline/native_project/imports.rs:942-1102`,
   whose values are mangled unique symbols, not bare names). Reuse it for the
   flattened lane instead of maintaining two schemes.
2. Or teach HIR lowering to consume `__simple_flatten_module_owner__=` and key
   `globals` / `module.functions` on `(owner, name)`.

(1) is preferred: the mechanism exists and is already proven in the native lane.

Note this defect is **not** alias-specific. Any flattened unit with two
same-named free functions is last-wins in codegen today; the alias case is
merely how it was caught.

## Unblock condition

The reproducer above prints `R:42` under `SIMPLE_JIT_STRICT=1`, the
`source_name == "main"` and duplicate-count guards in
`Lowerer::collect_flattened_import_aliases` are removed, and
`sh scripts/check/check-import-alias-codegen.shs` still PASSes 5/5.

## Do not

Do not close this by renaming `main` in `runtime_minimal.spl` or by rewriting
the six `cstart.spl` imports to plain imports. Both hide the defect; the alias
form is valid grammar and duplicate names across modules are legal.
