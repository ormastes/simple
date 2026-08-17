# native-build: trait-typed RETURN value as method receiver fails MIR lowering

- **Date:** 2026-08-09
- **Lane:** `native-build` (AOT / MIR lowering). NOT reproducible via
  `bin/simple test` — the tree-walk interpreter resolves these receivers fine.
- **Status:** OPEN. Root cause located; fix is a semantic policy decision
  (see "Why this was not fixed in place").
- **Repro fixture:** `test/fixtures/native_trait_receiver_resolution/main.spl`
- **Blocking decision doc:** `doc/02_requirements/language/type_system/native_trait_object_dispatch_options.md`

## Symptom

```
error: MIR lowering error: unresolved method call: greet
```

## Measured matrix

Binary: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`, which
self-reports as the **Rust bootstrap seed**. However `native-build` drives the
pure-Simple `src/compiler/**` lowering: the `[mir-method-call] ...` traces in
the build log are emitted by
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`. So the
results below are evidence about the pure-Simple MIR lowering on the native
lane, not about the seed's own codegen.

Command shape (each shape built in isolation, own cache dir):

```
env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_TIMEOUT_SECONDS=3600 \
  bin/simple native-build --source <dir> --entry-closure --entry <main.spl> \
  --cache-dir <cache> --output <bin>
```

| # | Receiver shape | Build | Run output | Verdict |
|---|---|---|---|---|
| A | trait-typed LOCAL var `var a: Greeter = FriendlyGreeter(...)` | rc=0 | `local A` | PASS |
| B | trait-typed struct FIELD `h.g.greet(...)` | rc=0 | `field B` | PASS |
| D | trait-typed OPTIONAL field `if val g = oh.g: g.greet(...)` | rc=0 | `" D"` | **WRONG VALUE** — `self.prefix` reads EMPTY (expected `optfield D`) |
| C | trait-typed RETURN value `make_greeter().greet(...)` | rc=1 | — | **HARD FAIL** `unresolved method call: greet` |
| A+B | both together | rc=0 | `local A` / `field B` | PASS |

**This corrects a prior belief.** The comment block in
`test/fixtures/native_trailing_default_param/main.spl` states that a
trait-typed FIELD receiver also hits this defect. Measurement says otherwise:
the plain field receiver (B) works, and the OPTIONAL field receiver (D) builds
but silently loses field data (D is a *separate, fail-open* defect and should
be filed/fixed on its own — it is strictly worse than C's loud failure).

## Root cause

The native lane has **no trait-object / vtable dispatch at all** —
`/usr/bin/grep -rlniE "vtable|vtbl|dyn_dispatch|trait_object"` over
`src/compiler/50.mir/` and `src/compiler/60.codegen/` returns **zero files**.
Every trait method call that works today works by *static devirtualization*:
MIR recovers the receiver's CONCRETE class name and rewrites the call to that
class's method symbol.

Semantics hands MIR `MethodResolution.Unresolved` for all of these (confirmed
in the build log: `[mir-method-call] resolution-enter method=greet
unresolved=true`, then `resolution-arm=unresolved`). So dispatch is decided
entirely by the Unresolved arm's owner-recovery block:

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2505-2546`

```
val unresolved_struct_name = self.struct_value_syms.get(unresolved_receiver_local.id)
if unresolved_struct_name != nil and unresolved_struct_name != "":
    val unresolved_method_key = "{unresolved_struct_name}::{method}"
    ... self.struct_method_syms.contains(unresolved_method_key) ...
```

- **Shape A** works because the struct-literal construction site writes
  `struct_value_syms[local] = "FriendlyGreeter"`, which is propagated across
  the local assignment.
- **Shape B** works via `remember_field_projection_provenance`
  (`method_calls_literals.spl:2308`).
- **Shape C fails** because the call-result local's provenance is registered
  from the callee's *declared* return type, not from any construction site:

  `src/compiler/50.mir/_MirLowering/module_lowering.spl:798-831` prescan
  ```
  match prescan_fn.return_type.kind:
      case Named(prescan_return_symbol_id, _):
          ... prescan_return_shape = self.composite_layout_key(prescan_return_symbol)
  bootstrap_fn_ret_shape_register(prescan_call_name, prescan_return_shape)
  ```
  For `fn make_greeter() -> Greeter` the declared return type is the **trait**,
  so the registered shape is `"Greeter"`.
  `remember_call_hir_return` (`_MirLoweringExpr/expr_dispatch.spl:1456-1462`)
  then sets `struct_value_syms[call_result] = "Greeter"`.

  Back in the Unresolved arm the key becomes `"Greeter::greet"` — but
  `struct_method_syms` is keyed by the **impl TARGET type**, i.e.
  `"FriendlyGreeter::greet"` (`module_lowering.spl:1127-1163`). Miss.
  The two remaining fallbacks also miss:
  - `receiver_declared_type(receiver)`
    (`_MirLoweringExpr/switch_operators_calls.spl:1710-1745`) handles **only**
    `Var`/`NamedVar` receivers; a `Call` receiver returns `nil`.
  - `lookup_or_invalid("Greeter")` resolves to the TRAIT symbol, whose
    `lookup_method_in_type` has no impl body to offer.

  Fall-through reaches `self.error("unresolved method call: {method}", nil)`
  at `method_calls_literals.spl:2933`.

### The load-bearing structural gap

`module_lowering.spl:1127-1163` walks `module.impls` and indexes every impl
method **only by its target type name**. `impl_def`'s trait reference is
**never recorded** — there is no trait -> impls index anywhere in MIR. So when
the recovered owner name turns out to be a trait, lowering has no way to ask
"which classes implement `Greeter`?"

## Why this was not fixed in place

The minimal mechanical fix is: in the `module.impls` loop, also build a
`trait_impl_syms["{TraitName}::{method}"] -> [method_id]` index, and in the
Unresolved arm, when the recovered owner name is a TRAIT, consult it.

That works only when the trait has **exactly one** impl in the program
(sound monomorphic devirtualization). With two or more impls the concrete type
is genuinely unknowable at compile time and the call needs real dynamic
dispatch, which this compiler does not have anywhere in MIR or codegen.

Landing the single-impl special case alone would create a silent capability
cliff — the same source compiles when a trait has one impl and hard-fails the
moment a second impl is added anywhere in the program. That is a language-level
policy call (does Simple's native lane support trait objects, and if not,
should it reject trait-typed returns/fields at the type level?), so it is filed
rather than guessed at.

## Fix recipe (when the policy decision is made)

1. `src/compiler/50.mir/_MirLowering/module_lowering.spl:1127-1163` — in the
   `module.impls` loop, additionally record the trait name from `impl_def`
   into a new `trait_impl_syms` map keyed `"{TraitName}::{method}"`, holding
   the LIST of candidate method ids (one per implementing type).
2. `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2540-2546`
   — extend the `final_unresolved_method_id == nil` fallback: if
   `trait_impl_syms` has the key and the candidate list has length 1,
   devirtualize to it.
3. If the candidate list has length > 1, replace the generic
   `unresolved method call: {method}` at line 2933 with a specific diagnostic
   naming the trait and the candidate count, so the failure is
   self-explanatory instead of looking like a missing builtin.
4. Fence with a `scripts/check/` script driving `native-build` over
   `test/fixtures/native_trait_receiver_resolution/` (with shape C
   uncommented) — no `*_spec.spl` can observe this lane, exactly as
   `scripts/check/check-native-trailing-default-param.shs` documents.

## Related / sibling defects to file separately

- **Shape D (fail-open):** trait-typed OPTIONAL field receiver builds and
  dispatches, but the callee reads `self.prefix` as EMPTY. Silent data loss on
  the native lane; higher severity than C.
- The Rust bootstrap seed was **not** inspected or modified. Whether the same
  gap exists in `src/compiler_rust/**` is unverified and is out of scope per
  the fix-`.spl`-not-the-seed rule.

## Re-triage 2026-08-17 (m9a_tests lane)

**Verdict: not re-measured; ownership note.**

Fixture `test/fixtures/native_trait_receiver_resolution/main.spl` is present.
The doc states the root cause is located and the fix is blocked on a semantic
policy decision recorded in `native_trait_object_dispatch_options.md` — i.e.
this is not an unknown-cause bug but a pending design decision.

The fix lives in MIR lowering (`src/compiler/50.mir/**`), which is owned by
another lane in the current parallel session, so this lane contributes
**diagnosis only** and made no edit.

**Not reproduced from this lane** — a native-build reproduction requires a
`native-build` run, and the one native-build lane this session attempted
(`check-native-crossmodule-result-u8.shs`, see that doc) was still executing
when this batch closed under a host load average of 81-133.
