# Stage-3 bootstrap E-MONO-032 blocker: walk_hir_* generic family (2026-10-09)

Batch record for the stage-3 (full one-binary closure via the admitted
stage-2 compiler) failure with 115 x E-MONO-032:

> call to generic `walk_hir_*` / `cas_batch_error_v1` has no explicit type
> arguments and they could not be inferred from its argument types; call site
> not monomorphized

Evidence log:
`.simple/storage/build/bootstrap/logs/aarch64-apple-darwin/stage3-native-build.log`
(run at `4140c247d78`; `git-state-before.env` head=4140c247d78,
`[mono] generic_fns=66 call_sites=124 specializations=3 unresolved=115`).
Local reproducers under `build/mono-probes/` (gitignored; key sources inlined
below). Strict = admitted stage-2 compiler
`.simple/storage/build/bootstrap/stage3/aarch64-apple-darwin/stage2-admitted/simple`
(Oct 9 18:07 admission). Seed = `src/compiler_rust/target/bootstrap/simple`.

## TL;DR

- `cas_batch_error_v1` family (34): **already fixed** — every call site was
  annotated by `03278930efc` and the current admitted stage-2 accepts the
  construct (probe `b_leaf` passes strict). The 4140 log predates the current
  admission; not a live blocker.
- `walk_hir_*` family (81): fixed in source on this branch. Root cause is a
  strict-monomorphizer substitution gap (**BUG B** below); the house-pattern
  fix (annotated accumulator local, PR #2693 style) makes the strict
  monomorphizer accept every walk site: validation closure reports
  `[mono] generic_fns=25 call_sites=225 specializations=22 unresolved=0`.
- **BUG C (compiler lane, NOT patched, release-blocking):** once mono accepts
  generic→generic call chains, the compiled binary **SIGBUSes at runtime on
  both cranelift and llvm**. Minimal repro inlined below; seed accepts and
  runs it correctly. Stage-3 build should now pass mono, but stage-3 runtime
  sanity will crash in HIR-walking paths until BUG C is fixed.

## Source fix (this branch)

Generator `src/app/compiler_schema/fold_gen.spl` (`emit_one_walk`) now emits
`var acc: C = f(...)` / `var acc: C = ctx` instead of unannotated
`var acc = ...`; regenerated `hir_visitor.spl` (25 walk fns) and
`ast_visitor.spl` (38 walk fns) accordingly, and annotated the one external
caller (`src/compiler/90.tools/sffi_audit/hir_inventory.spl:176`,
`walk_hir_block<SffiHirInventoryContext>(...)`; its `context` local is an
unannotated call result, so C could not bind — same class as #2693).
`hir_match_coverage.spl:236` was already annotated by `03278930efc`.

Why the annotation works: at every internal recursive call
(`acc = walk_hir_type(node.type_, acc, f)`), the strict monomorphizer's local
inference (`infer_call_type_args`) must bind `C` from the argument types.
`acc` (an unannotated `var`) has no local type, the node args carry no `C`,
and the callback arg's type is unusable (see BUG B), so nothing binds `C` →
fail-closed `[]` → E-MONO-032. `var acc: C` puts a concrete `C` (post-
substitution) into the inference env, binding `C` at every recursive site.
Explicit `<C>` at the internal call sites does NOT help: type arguments that
name an enclosing type parameter are dropped before mono sees them (the
E-MONO-032 text "has no explicit type arguments" is misleading there).

Note: the generated files also have pre-existing variant-ordering drift vs the
generator (a `FloatLexeme` arm position, present before this change); a full
regen sweeps it, but it was left untouched here to keep the diff minimal.

## BUG B (compiler lane, root cause, NOT patched): Function-typed param not substituted

`src/compiler/40.mono/monomorphize/type_subst.spl:136`:

```spl
case HirTypeKind.Function(ps, ret, _):
    HirType(kind: HirTypeKind.Function(ps, substitute_type(ret, subst), effects), ...)
```

Only the return type is substituted; the parameter list `ps` keeps
`TypeParam`s. A specialized walker's callback param stays
`fn(HirWalkNode, C) -> MyCtx` — non-concrete — which both starves inference
and, when it is read, binds `C` to the stale `TypeParam("C")` and conflicts
(`bind_type_params` already-bound arm). The source annotation works around
the starvation; fixing line 136 (substitute each of `ps`) removes the need
for the workaround.

## BUG C (compiler lane, NOT patched, release-blocking): generic→generic specialization chain miscompiles

Minimal repro (`build/mono-probes/a30_nofnptr/main.spl`, inlined; recursion is
bounded by the `v` counter):

```spl
class Expr:
    v: i64

class Blk:
    body: Expr

class MyCtx:
    n: i64

fn walk_block<C>(node: Blk, ctx: C) -> C:
    var acc: C = ctx
    acc = walk_expr(node.body, acc)
    acc

fn walk_expr<C>(node: Expr, ctx: C) -> C:
    var acc: C = ctx
    acc = MyCtx(n: acc.n + node.v)
    if node.v > 0:
        acc = walk_block(Blk(body: Expr(v: node.v - 1)), acc)
    acc

fn main() -> i64:
    val root = Expr(v: 2)
    val out: MyCtx = walk_expr<MyCtx>(root, MyCtx(n: 0))
    print("A30_OK n={out.n}")
    out.n
```

- Seed (interpreter): runs, prints `A30_OK n=3`.
- Strict native-build (cranelift AND `--backend llvm`): **build succeeds**
  (`[mono] generic_fns=2 call_sites=3 specializations=2 unresolved=0`, link
  OK), binary dies at startup:
  `Fatal: SIGBUS ... (si_code=1: misaligned address)`.
- Same with the two-walker fn-callback shape (`a26_twofn`, bounded, seed
  prints `A26_OK n=5`; strict binary SIGBUSes).
- Self-recursive specializations are fine (`a24`, `a25` compile and run
  correctly); the crash needs one *specialized* generic calling a *different*
  specialized generic. `hir_visitor` is exactly such a chain
  (walk_hir_expr → walk_hir_type/walk_hir_block/...), so a stage-3 binary
  would SIGBUS the first time it walks HIR (e.g. enum-contract match
  coverage) until this is fixed.

## BUG D (compiler lane, NOT patched): `T?` param poisons generic template registration

A generic function with an optional-sugar parameter (`fn f[C](node: i64?, ctx: C) -> C`)
fails E-MONO-032 at **every** call site — including fully explicit
`f<MyCtx>(1, ctx)` — while the identical function spelled `Option[i64]`
passes (`build/mono-probes/a11_optdecl` vs `a15_option`). The `T?` sugar on
a generic's parameter apparently derails template registration (the
`expected.len() != targs.len()` loud-fail in `rewrite_call`). Not exercised
by the walk_hir fix (walk signatures use plain class params), but a latent
trap for any future generic with `?` params. Seed accepts both spellings.

## Validation performed

- Strict (admitted stage-2) native-build of an entry importing
  `compiler.semantics.enum_contract.hir_match_coverage` (pulls generated
  `hir_visitor` + both external callers into the mono closure):
  `[mono] generic_fns=25 call_sites=225 specializations=22 unresolved=0` —
  previously every walk_hir_* internal call site was an E-MONO-032.
  (The build then stops in unrelated, pre-existing strict-MIR module-poison
  errors in `src/compiler/20.hir/hir_types.spl:51` — the documented
  module-diagnostics family, out of scope here.)
- Seed runs the same entry: `VAL_OK`.
- Fresh generator output vs committed files: identical except the
  pre-existing `FloatLexeme` ordering drift.
- Probe matrix (all under `build/mono-probes/`, seed=interpreter vs
  strict=native-build): `b_leaf` annotated leaf generic — strict PASS (proves
  cas_batch group fixed); `a20_realshape` unannotated walker — strict
  E-MONO-032 x3, seed OK; `a21/a25/a26` annotated walker variants — strict
  mono PASS; `a30` generic→generic chain — strict builds, binary SIGBUS,
  seed OK; `a11` vs `a15` — `?`-param poison vs `Option[]` OK.
