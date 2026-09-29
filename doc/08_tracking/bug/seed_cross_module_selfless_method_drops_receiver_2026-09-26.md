# Stage 2 admission SIGSEGV: cross-module call of a self-less method drops the receiver

- **Filed:** 2026-09-26
- **Status:** FIXED in the seed (`src/compiler_rust/compiler/src/pipeline/native_project/imports.rs`
  `method_arity`); Stage 2 lane result recorded at the end of this record.
- **Area:** Rust seed, native-project import arity table vs HIR implicit-`self`
  injection; cranelift `MethodCallStatic` receiver prepend
- **Host:** yoon-note, x86_64-unknown-linux-gnu
- **Reached after:** `seed_cranelift_bare_return_in_inferred_any_fn_traps_2026-09-26.md`
  (the first blocker of the day; this one was masked behind it).

## Symptom

With the bare-`return` fix in the seed, Stage 2 builds a new candidate
(sha `cbe5f9…`) and the admission probe advances past `phase=parse` and
`aop_weave`, then dies in `phase=native_cache` at 153 ms:
`candidate_frontend_smoke: hello-world-positional-build failed (raw rc=139)`.
Exact replay under `run_capped.shs` `CAP_MEM_MAX=4G`: rc=139, 0.36 s wall,
**51 MB** peak RSS (again not a memory problem).

gdb on the candidate:

```
#0 compiler.driver.cache.native_module_witness.native_module_cache_witness_v1 ()   mov (%rdx),%r12  with rdx=0x38
#1 compiler__driver__cache__native_module_witness_facts__NativeModuleCacheFactSetV1_dot_witness ()
#2 compiler.driver.driver_aot_native_output.driver_native_shadow_witness_v1 ()
```

The faulting load is the `config` parameter (`0x138(%rsp)`, `and ~7`, deref);
`config` arrived as the integer `0x38`. `NativeModuleCacheFactSetV1.witness`
(`native_module_witness_facts.spl:27`) is a struct method declared WITHOUT
`self` whose body reads `self.valid`, called from another module
(`driver_aot_native_output.spl:306`, `complete_facts.witness(mir_identity, config)`).

## Root cause (12-line two-module reproducer, machine-level confirmation)

```
# facts.spl                                   # main.spl
struct FactSet:                               use facts.{make_facts}
    module_id: text                           fn main():
    valid: bool                                   val fs = make_facts("m1")
    fn three(a: text, b: text, c: text) -> text:  print(fs.three("A1", "B2", "C3"))
        "a=" + a + " b=" + b + " c=" + c + " self=" + self.module_id
```

Built with the seed exactly as Stage 2 builds (`SIMPLE_NATIVE_BUILD_RUST=1
--backend cranelift --runtime-bundle core-c-bootstrap --mode one-binary`):

| seed | output |
|---|---|
| 09-19 `bin/simple` | `a=B2 b=C3 c=0 self=<value:0x1535…>` — silently shifted |
| 09-26 rebuilt | same shift; with a struct argument (`cfg: Cfg`) the shifted `self.field` read SIGSEGVs |
| same file (single module) | `a=A1 b=B2 c=C3 self=m1` — correct |

`objdump`: the caller sets `rdi=A1, rsi=B2, rdx=C3` and calls
`facts__FactSet_dot_witness`; the callee prologue reads `rdi` as `self`,
then `rsi, rdx, rcx`. Three arguments were passed to a four-parameter callee.

Three rules disagree about a self-less method that uses `self`:

1. **Parser** (`parser/src/types_def/mod.rs:725-728`): no `self`/`me` param
   and not a `me` method ⇒ `f.is_static = true` (no injection).
2. **HIR definition side** (`hir/lower/module_lowering/function.rs:986-988`):
   `inject_implicit_self = owner && !has_self && (!is_static || body_uses_self)`
   ⇒ the callee is compiled with `(self, a, b, c)`.
3. **Native-project import arity** (`pipeline/native_project/imports.rs`
   `method_arity`): `params.len() + (!is_static && no self)` ⇒ declares the
   imported symbol with **3** params.

The cranelift call site (`codegen/instr/closures_structs.rs:1170`) prepends
the receiver only when `sig_params != args.len()`, so with a 3-param import
declaration and 3 explicit args the receiver is dropped. Same-module calls
resolve the local `MirFunction` (4 params) and are correct. The 1-arg
default-fill path (`hir/lower/expr/mod.rs:1052`) happened to pass the receiver
correctly, which is why the original stage-2 backtrace looked like a
default-argument problem — it is not; `e_method_nodefault` (no default at all)
reproduces identically.

Not introduced today: the 09-19 seed miscompiles the same shape silently. The
09-25 parser change `df9f0ef20ca` (self-less `fn new` is static) did not
create rule 1 — it only removed the `new` exception.

## Fix

`imports.rs` `method_arity` now mirrors rule 2 exactly:
`params.len() + (no explicit self && (!is_static || block_uses_self(&body)))`,
with `block_uses_self` exposed `pub(crate)` from
`hir/lower/module_lowering/function.rs` (re-exported through
`module_lowering/mod.rs` and `hir/lower/mod.rs`). `cargo check --release
--bin simple` clean.

## Specs

- `test/01_unit/compiler/backend/cross_module_selfless_method_receiver_spec.spl`
  — reproducing: native-builds the two-module fixture through `bin/simple`
  and asserts the exact transcript (`a=A1 b=B2 c=C3 self=m1`, then the
  struct-argument `witness` line). On the unfixed 09-19 seed:
  `outcome=ERROR executed=1 failed=1`, got `a=B2 b=C3 c=0…`.

## Still open (not fixed here)

- `hir/lower/expr/calls.rs:279` / `expr/mod.rs:1052`: an OMITTED trailing
  argument whose default is not a constant (e.g. a struct constructor
  `Cfg(...)`) is "left unfilled" — the call is then emitted with fewer
  arguments than the callee has parameters, and the callee reads garbage.
  Reproduced (`c_method_default`, `d_free_default` in the same investigation):
  SIGSEGV on the 09-26 seed, `cfg.field == 0` on the 09-19 seed. The
  interpreter evaluates the default in the callee and is correct. This is
  the third defect in this family and needs its own fix (either lower
  constant-argument constructor defaults at the call site, or refuse the
  compile instead of emitting a short call).
