# Trait conformance check is name-only — arity and parameter types are never compared

- **Status:** OPEN (mechanism confirmed; one instance of the resulting drift fixed)
- **Found:** 2026-08-04, while closing the `MirTextCodegen` / `MirToLlvm` break (`4670db2d31f2`)
- **Severity:** latent, repo-wide. A trait declaration can disagree with its
  implementer on argument count and the compiler stays silent.

## Summary

`impl <Trait> for <Type>` is accepted whenever the impl defines a method with
the *same name* as each abstract trait method. Nothing compares the parameter
list. A trait may declare `f(a, b)` while its only implementer defines
`f(a, b, c)`; the impl is accepted, and callers written against the trait's
declared 2-arg shape are then wrong in a way the declaration does not reveal.

## The check

`src/compiler_rust/compiler/src/interpreter_eval.rs:985`

```rust
let impl_method_names: std::collections::HashSet<_> =
    impl_block.methods.iter().map(|m| m.name.clone()).collect();

for trait_method in &trait_def.methods {
    if trait_method.is_abstract && !impl_method_names.contains(&trait_method.name) {
        return Err(crate::error::factory::missing_trait_method(
            &type_name, &trait_method.name, trait_name,
        ));
    }
}
```

Three properties follow directly from this code and are all confirmed by probe:

1. **Name-only.** The set is built from `m.name`. `m.params` is never read, so
   arity, parameter names, parameter types and return type are all unchecked.
2. **First-failure-only.** `return Err(...)` inside the loop, so a drift of N
   methods surfaces as N sequential one-method errors — this is why the
   `MirTextCodegen` three-method break read as a one-method problem.
3. **Interpreter-path only.** The check lives in `interpreter_eval.rs`. Under
   the default JIT engine it does not run at all.

The pure-Simple side has an equivalent name-only validator at
`src/compiler/25.traits/trait_impl.spl:120` (`validate_methods`, `self.has_method(method.name)`),
but it has **no callers** anywhere in `src/` — as does
`src/compiler/00.common/error.spl:516` (`missing_trait_method`). The live check
is the Rust one above.

## Probe evidence

Probes in `scratchpad/arity_probes/`. Run with the deployed
`bin/release/x86_64-unknown-linux-gnu/simple`.

| probe | shape | `bin/simple run` (JIT, default) | `SIMPLE_EXECUTION_MODE=interpret` |
|---|---|---|---|
| `p2_control` | trait 3-arg, impl 3-arg, call 3-arg | exit 0, `p2 result=7` | exit 0, `p2 result=7` |
| `p1_trait_arity` | trait declares `f(a,b)`, impl defines `f(a,b,c)`, call `f(1,2)` | **exit 0, `p1 result=6`** | exit 1, `error: semantic: function expects argument for parameter 'c', but none was provided` |
| `p3_plain_underarg` | no trait; 3-arg method, 2-arg call | **exit 0, `p3 result=6`** | exit 1, same arity error |
| `p4_missing_method` | trait declares `g`, impl omits it | **exit 0, `p4 result=3`** | exit 1, `error: semantic: type `C` does not implement required method `g` from trait `T`` |
| `p5_sibling_overload` | sibling class also has a 2-arg `f`; call 2-arg on the 3-arg class | **exit 0, `p5 result=6`** | exit 1, same arity error |
| `p6_selfcall_in_impl` | `self.f("z", 7)` where `f` is 3-arg | **exit 0, `p6 result=10`** | exit 1, `...parameter 'span'...` |

Two independent facts fall out:

- **The trait/impl arity mismatch itself is never reported, in either engine.**
  In `p1` the interpreter's complaint is about the *call site*, not about the
  impl disagreeing with the trait it claims to satisfy. Remove the bad call and
  the mismatched impl is accepted with no diagnostic at all.
- **Under JIT a missing trailing argument reads as the nil sentinel `3`.**
  `p1`/`p3`/`p5` return `1+2+3 = 6`; `p6` returns `7+3 = 10`. That is the same
  sentinel documented in `nil_sentinel_3_forbids_defaulted_int_args`. It is a
  silent wrong value, not a crash and not a nil.
- **The interpreter's call-site arity check is evaluation-time, not static.**
  It fires only when the bad call is actually executed, so a bad call on a cold
  path (as both real ones below were) passes every `bin/simple test` run.

## Instance found and fixed

`translate_function`, trait `MirTextCodegen`:

| site | signature / call | file:line |
|---|---|---|
| trait decl | `me translate_function(name: text, body: MirBody)` | `src/compiler/70.backend/backend/common/mir_text_codegen.spl:22` |
| impl (only implementer) | `me translate_function(name: text, body: MirBody, span: Span)` | `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:349` |
| call site | `self.translate_function(name, body)` | `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:347` |
| call site | `translator.translate_function(... , body)` | `src/compiler/80.driver/driver_bootstrap.spl:479` |

Both call sites are on the flat-bootstrap AOT path. `span` is read only under
`if self.debug_info:` (`core_codegen.spl:502`), and neither bootstrap translator
(`driver_bootstrap.spl:340`, `:456`) calls `enable_debug_info()` — that happens
only in `llvm_backend.spl:282` and `llvm_codegen_adapter.spl:48/93`. So the
under-arity calls were inert *by accident*: nothing read the sentinel.

Fixed by aligning the declaration with the sole implementer and giving both call
sites a real third argument. `driver_bootstrap.spl:479` now passes `fn_.span`,
matching the sibling loop at `core_codegen.spl:303`.
`core_codegen.spl:347` passes `Span.empty()` — flat-bootstrap bodies come from
`MirBody.from_bootstrap_parts`, which carries no function-level span, and
`Span.empty()` has `line: 0`, so `if span.line > 0: span.line else: 1` yields
the same `dbg_line = 1` the nil branch already produced. No behaviour change on
either path.

## Sweep: how widespread is the drift

Method: parse every `trait X:` block and every `impl T for Y:` block at column
0 across owned `src/**.spl` (excluding `src/compiler_rust/` and `vendor/`),
accumulate each `me`/`fn` signature across line continuations, drop a leading
`self`/`me` parameter so the `fn f(self, ...)` and `me f(...)` conventions
compare equal, and report name matches whose arity differs.

**Result: 30 drifted method pairs across 4 traits.**

| trait | drifted methods | impls affected |
|---|---|---|
| `BlockDevice` (`src/os/drivers/nvme/block_device.spl:17`) | `read_sector` — declared `(lba: u64, buf_phys: u64) -> Result<bool, text>`, every impl defines `(lba: u64) -> Result<[u8], text>` (return type differs too) | 9 |
| `RenderBackend3D` (`src/lib/nogc_sync_mut/engine/render/backend3d.spl`) | `bind_texture` 3-arg decl vs 2-arg impls; `create_pipeline` 1-arg decl vs 4-arg impls; `end_render_pass` 1-arg decl vs 0-arg impls | 12 classes |
| `RenderBackend` (`src/lib/nogc_async_mut/gpu/engine2d/backend.spl:33`) | `init` 2-arg decl vs 0-arg impls | 2 |
| `MirTextCodegen` | `translate_function` (fixed here) | 1 |

Spot-checked by reading the trait and impl source for `BlockDevice`,
`RenderBackend3D` and `RenderBackend` — all real, none a parser artifact.

**Error modes of this sweep (the 30 is a lower bound, not a census):**

- Only the `impl Trait for Type:` form is matched. The repo also uses
  `impl ClassName: TraitName` (see the comment at `backend3d.spl:70`); those
  blocks are classified inherent and skipped. 552 `impl X for Y` headers exist
  against 5,024 `impl X:` headers, so most impl blocks are not examined.
- Traits are keyed by bare name, so two traits sharing a name in different
  files collide and one shadows the other.
- 158 of the repo's 300 `trait` declarations were parsed; the rest are nested,
  indented, or generic-parameterised in a form the header regex misses.
- Return-type and parameter-type drift is not scored at all — only arity. The
  `BlockDevice` case shows type drift travels with arity drift, so the true
  defect count is at least 30.

Only the `MirTextCodegen` entry is touched by this change. The other 29 are
reported, not fixed: each needs its own owner to decide whether the trait or the
impls are authoritative, and `RenderBackend3D`/`RenderBackend` are live GPU
lanes under active work.

## Recommendation

Do **not** bolt full signature type-checking onto this. The minimal, targeted
fix is at `interpreter_eval.rs:985`: alongside the name-set membership test,
compare `trait_method.params.len()` against the matched impl method's
`params.len()` (after normalising the `self`/`me` receiver) and emit a distinct
error naming both arities. That is a purely additive check on a path that
already walks both signatures, it would have caught all 30 pairs above, and it
costs nothing at runtime.

Two follow-ups worth filing separately:

1. Collect *all* conformance failures for one impl before returning, instead of
   `return Err` on the first. The one-at-a-time reporting turned a three-method
   break into three sequential debugging rounds.
2. `validate_methods` (`src/compiler/25.traits/trait_impl.spl:120`) and
   `missing_trait_method` (`src/compiler/00.common/error.spl:516`) are the
   pure-Simple equivalents and have **no callers**. Either wire them up as the
   self-hosted conformance check — the right place for the arity comparison
   above, per *Fix .spl not Rust* — or delete them; leaving an uncalled
   validator next to a live Rust one invites the next reader to fix the wrong
   copy.
