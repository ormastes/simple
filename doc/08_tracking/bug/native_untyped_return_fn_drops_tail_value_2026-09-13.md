# A function with no declared return type returns 0 in native codegen
## Status: FIXED (2026-11-11, lane ne17) — fix of 2026-11-06 verified on fresh
## seed 46fe8f6b6def; the one remaining red example in the evidence spec is a
## distinct fresh-seed visibility defect (see addendum), not this row's
## behavior. Pure-Simple native e2e + differential harness still pending.

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Filed: 2026-09-13
- Found by: reducing the `crash` class of
  `doc/10_metrics/infra/native_interp_differential_2026-09-13.md`
- Lane: `SIMPLE_NATIVE_BUILD_RUST=1 <seed> native-build --mode dynload --backend cranelift`
- Class: `other` (was hidden behind the `crash` class until the SEGV was fixed)
- Status: OPEN — reduced, not fixed

## Symptom

A function whose return type is not written down returns its tail expression
under the interpreter and **0** under native codegen. Its typed twin is correct,
so the discriminator is the missing annotation alone.

```simple
fn mk_untyped():
    var c = []
    c.push(7)
    c

fn mk_typed() -> [i64]:
    var c = []
    c.push(7)
    c

fn main():
    val a = mk_untyped()
    print("untyped val={a} len={a.len()}")
    val b = mk_typed()
    print("typed   val={b} len={b.len()}")
```

| lane | untyped | typed |
|---|---|---|
| interpreter | `val=[7] len=1` | `val=[7] len=1` |
| native (cranelift, dynload) | `val=0 len=<value:0xffffffffffffffff>` | `val=[7] len=1` |

`len=-1` is the downstream consequence, not a second defect: the caller holds
`0`, which carries no collection tag, and the tag-dispatching length helper
answers `-1` for an unrecognised receiver.

## Reproducer

```sh
SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1 \
  build/cargo-f52/release/simple native-build \
  --source src/lib --entry-closure --mode dynload --backend cranelift \
  --threads 1 --entry <the file above> -o /tmp/a.out
/tmp/a.out
```

Interpreter control: `SIMPLE_EXECUTION_MODE=interpreter <seed> run <same file>`.

## Where it is NOT

The ABI is innocent. `build_mir_signature`
(`src/compiler_rust/compiler/src/codegen/shared.rs:180-190`) unconditionally
gives every non-`main` function one `I64` result, and its own comment states the
intent exactly — *"Simple semantics guarantee every function returns a value
(nil when no explicit return), and MIR return_type is VOID for inferred-return
functions"*. So the slot to carry the value exists and is the right width; the
value never reaches it. The defect is upstream, where the body's tail
expression is turned into the return terminator for a function whose declared
return type is `TypeId::VOID`.

## Why it was invisible until now

It sat behind
`doc/08_tracking/bug/native_stringbuilder_to_text_segv_null_receiver_2026-09-13.md`.
An un-annotated function's result is `TypeId::VOID`, so a method call on it
reached codegen spelled `void.len` — and that pseudo-qualifier defeated the
erased-receiver builtin policies, rebinding the call to a linked
`StringBuilder.len` and crashing before any wrong value could be observed. With
that rebind fixed the program no longer SEGVs and this divergence is what is
left, which is why the two are filed separately rather than as one.

## Blast radius, stated rather than guessed

`src/lib/common/text_advanced.spl` alone has several un-annotated
value-returning functions (`char_frequency`, the `counts` builders), and the
idiom is common across the stdlib. Any native caller of such a function reads
`0`. This is a plausible contributor to the census's `other` class and should be
measured against it once fixed — but it has **not** been shown to be the cause
of any specific `other` row here, and that claim is deliberately not made.

## Fixing it

The fix belongs where the return terminator is built from the function body, not
in the backend: a tail expression must be returned whether or not a return type
was written. Because it changes the MIR of every un-annotated function in the
tree, it needs the full differential harness
(`scripts/check/check-native-interp-differential.shs`) run before and after, not
a spot check.


## Decision (2026-11-06, owner decision)

A function without `-> T` infers its return type from its last expression when
possible. When inference is impossible the compiler emits a diagnostic, never a
silent Unit. In robust mode a missing return type on a value-returning function
is a compile error.

- **Robust mode selection:** the resolved assurance policy
  (`ctx.assurance_policy.strictness >= Robust`; project `lints: profile:`, CLI
  flag, or `SIMPLE_SAFETY_PROFILE` for child processes — raise-only, see
  `src/compiler/00.common/assurance/policy.spl`). The driver passes it per
  invocation as `HirLowering.require_declared_return_type`
  (`driver_hir_requires_declared_return_type`, all five HIR lowering sites);
  the lowering default stays `false`. The HIR source-body cache identity folds
  the flag so robust and default lowerings never share an entry.
- **Pure-Simple compiler** (`infer_untyped_return_type` ->
  `tail_value_return_type_v1`, signature pass, so callers see the type): a
  side-effect-free value tail (literal, local, operator, cast, field/index,
  collection/struct literal, `??`, `?.`, comprehension) promotes the return
  type. A resolvable scalar (`i64`/`f64`/`text`/`bool`/...) is used directly,
  including through an unannotated binding initializer (`val x = 5; x`). An
  un-inferrable value tail (the bug's `var c = []; ...; c`) returns `Any`
  dynamically and reports `[W-RET-INFER-001]`. Calls, method calls,
  `if`/`match` and blocks keep the Unit default (they may be procedures); a
  sole string literal is a docstring. Robust mode reports `[E-RET-DECL-001]`.
- **Rust seed** (interpreter, JIT, cranelift native-build): already returns the
  tail (`body_produces_value` -> `TypeId::ANY`,
  `hir/lower/module_lowering/function.rs`). Re-verified 2026-11-06 on Windows:
  the reproducer above prints `untyped val=[7] len=1` under interpreter, JIT
  and `native-build --backend cranelift --mode dynload`. The seed is
  bootstrap-only, so robust-mode enforcement lives in the pure-Simple driver.
- **Evidence:** `test/01_unit/compiler/hir/untyped_tail_return_infer_spec.spl`
  (14/14; red before the change). Neighbouring untyped-return specs stay green.
- **Pending:** pure-Simple native end-to-end on a deployed self-hosted binary,
  and the differential harness run requested above.

## Addendum 2026-11-11 (lane ne17) — FIXED verified on fresh seed; one
## unrelated example masked by a distinct seed defect

`test/01_unit/compiler/hir/untyped_tail_return_infer_spec.spl` on fresh seed
46fe8f6b6def (Windows, worktree simple-p3-ne17-20261111,
`test --mode=interpreter --no-cache`): **16 executed, 15 passed** — including
both bug-shape examples ("bare local tail is not dropped to Unit",
"un-inferrable tail type is reported, never silent") and all robust-mode and
driver-flag examples. The untyped-return behavior this row records is fixed.

The single red example ("gives an explicit unit tail a Unit MIR signature,
matching its bare returns") fails NOT on this row's behavior but on a
distinct fresh-seed defect:

```
semantic: private fn `compiler_value_discriminant` of module
`\?\C:\...\src\compiler\00.common\value_access.spl` is not visible to
\?\C:\...\src\compiler\50.mir\_MirLoweringExpr\expr_dispatch.spl;
mark it `pub` or `export` it
```

Controls run in-lane: plain, generic, and `@inline` private cross-module
imports in a minimal probe all PASS; the tree PINS these wrappers non-pub
(`test/01_unit/compiler/mir/value_access_ownership_spec.spl` asserts the
facade contains no `pub fn compiler_value_`, and the module header documents
cross-module import of the wrappers as the design), and marking them `pub`
(tried, reverted) merely moves the red example to the pinning spec. This is
a seed-lane defect (Windows module-identity/visibility escalation, both
module paths `\?`-prefixed in the error) to route — not this row.

Pending items from the 2026-11-06 decision, unchanged and blocked on this
lane: pure-Simple native end-to-end on a deployed self-hosted binary, and
the `check-native-interp-differential.shs` harness run (native-build lanes
not granted here).
