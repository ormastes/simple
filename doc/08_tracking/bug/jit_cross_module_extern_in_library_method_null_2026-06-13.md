# JIT: undefined cross-module symbol binds NULL and SIGSEGVs (crash FIXED via guard)

- **Date:** 2026-06-13
- **Severity:** P1 crash — **FIXED** (JIT now falls back to interpreter instead of crashing). Native-codegen *feature* gaps remain (see Follow-ups).
- **Status:** Crash guarded/fixed; feature follow-ups Open.
- **Area:** codegen / cranelift JIT symbol binding; module import flattening.

> **NOTE — original diagnosis was WRONG.** This file first blamed a runtime
> `rt_*` extern's GOT slot ("extern referenced only in an imported library
> method body binds NULL"). That is **disproven**. The defect is **not
> extern-specific** and not about `referenced_names`. Corrected below.

## Symptom

Calling a method on a class imported from another module crashes in JIT/default
mode (SIGSEGV, exit 139); interpreter works. Minimal repro:

```
use std.common.string_builder
fn main():
    val b = RtStringBuilder.new()   # or StringBuilder.new() — same crash
    b.push("hi")
    print(b.finish())
```

## Corrected root cause (verified empirically)

- **Not extern-specific.** The non-extern `StringBuilder.new()` (array-backed,
  no `rt_*` calls) crashes identically. A class with a `static fn new()` defined
  in the **same file** works. So the trigger is *cross-module class method*, not
  the extern.
- The undefined symbol is the **class method**, not the extern: AOT reports
  `Undefined symbol: RtStringBuilder_dot_new (required by relocation 0)` — i.e.
  `RtStringBuilder.new` (`.`→`_dot_`), the constructor, has no definition.
- **Why no definition:** a whole-module `use std.common.string_builder` import
  (no `{group}`, no `*` glob) does **not** flatten the module's `impl` method
  bodies into the codegen unit. `should_flatten_nested_import`
  (`pipeline/module_loader.rs`) returns `false` for `ImportTarget::Single`/
  `Aliased`; only `Group`/`Glob(*)` flatten. The class *type* is available
  (via the exports cache) so type-checking, the interpreter, and direct
  `Type(field: …)` field construction all work — but the **method bodies are
  never compiled**, leaving `RtStringBuilder_dot_new` an undefined `Import`.
- **AOT vs JIT divergence:** AOT's SMF loader detects the undefined relocation
  and errors cleanly (exit 1). JIT does **not**: cranelift-jit fills an
  undefined `Linkage::Import`'s GOT slot with
  `lookup_symbol(name).unwrap_or(std::ptr::null())`
  (`vendor/cranelift-jit/src/backend.rs` `declare_function`), so the slot is
  NULL and the call jumps to 0 → SIGSEGV.

## Fix landed (the crash)

`src/compiler_rust/compiler/src/codegen/jit.rs` — `compile_module` now runs a
pre-finalize guard `first_unresolved_import()`: it enumerates declared
`Linkage::Import` functions (`module.declarations().get_functions()`) and checks
each resolves via the runtime provider **or** `dlsym(RTLD_DEFAULT)` — exactly
cranelift-jit's own `lookup_symbol` logic. If any import would bind NULL, the
JIT compile returns an error, so the driver's existing interpreter fallback runs
(`driver/src/exec_core.rs` `run_file_with_args`). This only fires where code
*currently hard-crashes*; it cannot regress a JIT path that already works.

Verified (release build): crash repro now prints `hi` (exit 0) via fallback;
direct `rt_*` extern call from `main` still JITs with **no** fallback; a local
class `.new()` still JITs; a no-import program still JITs; AOT still emits its
clean `Undefined symbol` error.

### Bonus: caught + fixed a second latent NULL-jump (`rt_dict_insert`)

Dict-literal programs (`{"a": 1}` + index) **also** SIGSEGV'd in JIT pre-guard:
MIR lowering emits a call to `rt_dict_insert`
(`mir/lower/lowering_expr_collection.rs:397`) but the runtime defines only
`rt_dict_set`/`rt_dict_new` (the LLVM backend works around this —
`codegen/llvm/functions/collections.rs:125` — but cranelift JIT did not).
**Fixed:** added `rt_dict_insert` → `rt_dict_set` to `sffi_alias_target`
(`codegen/instr/calls.rs`; exact 3-arg `(dict, key, value)` shape match), so
dict literals with statically-typed values now JIT **natively** (verified: a
`for k in d.keys(): t += d[k]` program prints the correct sum with no fallback).

### Guard scope / known conservative fallbacks

The guard fails the JIT compile if **any** declared `Import` is unresolvable —
even one that would never be *called* at runtime. This is conservative but
always correctness-preserving (the interpreter fallback produces identical
output). Measured blast radius over 40 real `examples/` programs: 0 new crashes,
**1** new JIT→interpreter demotion
(`examples/07_ml/torch/basics/01_tensor_creation.spl` — declares the unflattened
imported method `TorchTensorWrapper_dot_tensor_zeros` but never calls it in
torch-stub mode; output byte-identical pre/post). The other examples that fall
back already did so pre-guard for unrelated reasons.

Remaining unregistered codegen helpers that the guard now safely defers (NOT
chased individually — the guard handles the whole class): e.g. `rt_any_add`
(dynamic `any + any`, e.g. `dict[k] + dict[k]`). These are pre-existing
JIT-crash hazards now converted to correct interpreter fallback.

## Follow-ups (Open — native codegen feature, NOT the crash)

1. **Import flattening:** make a whole-module `use a.b.c` import flatten the
   used class's `impl` method bodies into the codegen unit (or require
   `use a.b.c.{Class}` / `.*`), so imported class methods JIT/AOT natively
   instead of falling back. (`should_flatten_nested_import`,
   `pipeline/module_loader.rs`.)
2. **Self-mutation lowering:** with a flattening import, JIT then fails with
   `cannot modify self in immutable fn method 'RtStringBuilder.finish'` because
   `finish()`/`free()` do `me.handle = 0`. Self-mutating methods need to lower
   correctly. Blocks native `RtStringBuilder` even once flattened.
3. **`rt_dict_insert`:** ~~MIR lowering emits a symbol the runtime does not
   define~~ — **FIXED** via `sffi_alias_target` alias to `rt_dict_set`. Dict
   literals with statically-typed values now JIT natively. (Dynamic-value dicts
   may still fall back on `rt_any_add` etc. — see below.)

## Impact / workaround

- JIT no longer crashes on an undefined cross-module symbol — it falls back to
  the interpreter (correct output, slower). No more exit-139.
- Native/JIT use of imported class **methods** still needs follow-ups 1+2; until
  then such code runs correctly under the interpreter. Do **not** wire
  `RtStringBuilder` into JIT/native hot paths (e.g. the MCP JSON builders) —
  see `rt_string_concat_quadratic_2026-06-12.md`.

## Cross-references

- `rt_string_concat_quadratic_2026-06-12.md` (H1 primitive; surfaced this)
- `codegen/jit.rs` `first_unresolved_import` (the guard)
- `pipeline/module_loader.rs` `should_flatten_nested_import` (flatten gate)
- `mir/lower/lowering_expr_collection.rs:397` (`rt_dict_insert` follow-up)
