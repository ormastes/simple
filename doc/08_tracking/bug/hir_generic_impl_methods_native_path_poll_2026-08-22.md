# HIR: generic impl methods still gated on the native path — `async/poll.spl` (2026-08-22)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status: OPEN** (filed; not fixed). Class 3 of the stage1-closure HIR fatals.

## Exact text
```
HIR lowering error in src/lib/nogc_async_mut/async/poll.spl: generic struct/class methods are not supported on the native build path yet: impl for a type with type parameter(s) declares method(s); monomorphization is not implemented (#158 Phase B)
```
Emitted by `src/compiler/20.hir/hir_lowering/_Items/trait_impl_lowering.spl`
(`if type_params.len() > 0: self.error(...)`) for

```
enum Poll<T>:
    Ready(T)
    Pending
impl Poll<T>:
    fn is_ready() -> bool
    fn is_pending() -> bool
    fn unwrap() -> T
```

## Is poll.spl in the bootstrap closure?
Yes for the full stage1 closure (`--source src/app --entry-closure --entry
src/app/cli/bootstrap_main.spl`): the probe log
`scratchpad/probe/driver_pre.log` parses `src/lib/nogc_async_mut/async/poll.spl`
(parse 613/687). It is NOT in the older fp9 closure log
(`scratchpad/fp9/stage1_build.log`, 667 files, 0 hits) — the closure grew
between the two trees. Reach chain (all `src/lib`):
`std.async` facade (`nogc_async_mut/async.spl:24`, `async_core.spl:11`,
`async/__init__.spl:243`) -> `std.async.poll.{Poll}`; also
`async/future.spl:5`, `async/runtime.spl:13`, `async/combinators.spl:6`,
`dns/resolver.spl:30`. The compiler-side entry into that subtree is
`src/compiler/20.hir/hir_lowering/async_errors.spl` (imports `async.future`).

## Module list: generic impls in the 687-file closure
Scan of every parsed closure file for `^impl X<...>`:
- `src/lib/nogc_async_mut/async/poll.spl:14: impl Poll<T>` — **the only one**.
The generic ENUM `Poll<T>` itself lowers (no enum-tier gate fires); only the
impl-tier gate does.

## Why 40.mono was not extended here (experiment)
625c245bafa (Phase B) specializes FREE generic fns by call-site type args.
Impl methods of a generic owner are already marked `is_generic_template` in
`trait_impl_lowering.spl` but the gate still fires. Removing only the gate and
native-building a 7-line `Poll<i64>` user (`p.is_ready()` / `p.unwrap()`)
gives `[mono] generic_fns=0 call_sites=0 specializations=0` and then
`MIR lowering error: unresolved method call: is_ready` (3x) — impl methods are
not in `module.functions`, so the pass never sees them, and method calls on a
generic receiver have no instantiation path. A real fix needs: (1) collect
impl-method templates from `HirImpl`, (2) derive type args from the RECEIVER
type at `MethodCall` sites, (3) specialize + repoint the method by mangled
name, (4) `prune_consumed_templates` for impl methods. That is a new feature
(#158 Phase C), not a minimal extension; the gate is left in place so the
failure stays loud and attributed to poll.spl.

## Cheapest unblocking alternative (not taken without approval)
`Poll<T>` has 3 methods and every closure call site could be rewritten
non-generically (`match p: case Poll.Ready(_)`), or the impl could be moved
out of the closure; both change stdlib API shape and were not done here.


---

## Addendum 2026-11-11 — lane compiler2 — verdict SUPERSEDED (gate removed; #158 landed)

Triage-first pass, batch 2. The reported HIR gate no longer exists on the
refreshed seed (build-commit 0791c2b7f4a7).

**The exact error is gone from source.** `trait_impl_lowering.spl` no longer
calls `self.error(...)` for "generic struct/class methods are not supported on
the native build path yet." Both the trait tier (:144-145) and the impl tier
(:348-349) now do `if type_params.len() > 0: hir_fn.is_generic_template = true`
(#158 Phase B marking) — the loud fatal this doc described was replaced by
template marking, and #158 monomorphization machinery has since landed, e.g.
`c9294577eff5` (substitute receiver type args into generic method return types,
2026-11-09), `6672f9336413` (exempt bare generic impl owner headers from nominal
arity), `7c03cb625fa3` (module-scoped monomorphization / COMDAT). The impl for
a type-with-type-params declaring methods is now a template consumed by the mono
path, not a hard error.

**Seed-smoke (HIR lane, green):**
`test/01_unit/compiler/20.hir/generic_enum_self_match_spec.spl`
(`--mode=interpreter --no-cache`) -> `outcome=OK, passed=5/5` — generic-enum
self-match (the `Poll<T>`-shape) lowers at HIR with NO gate diagnostic. Evidence
log: `build/review/p3c2-genenum-seedsmoke.log`.

**Verification caveats (honest):**
- The true end-to-end oracle — a native build of a `Poll<i64>` user — was NOT
  run (heavy entry-closure native build; blocked under this lane's mandate).
- The MIR-level generic specs that would exercise the full native path,
  `test/01_unit/compiler/50.mir/poll_payload_typeparam_match_spec.spl` and
  `generic_method_return_subst_spec.spl`, currently ERROR on an UNRELATED
  pre-existing compiler-source visibility defect: private generic fn
  `compiler_value_discriminant` (`src/compiler/00.common/value_access.spl:29`)
  is imported/used by `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:54,61`.
  That is a separate compiler bug (flagged to the parent), NOT bug 7 — the
  generic-impl specs get PAST the HIR gate and only then hit it. Logs:
  `build/review/p3c2-pollmono-seedsmoke.log`, `build/review/p3c2-genmethreturn-seedsmoke.log`.

**Cycles:** 0 (no fix attempted; defect already addressed in source).
