# HIR: generic impl methods still gated on the native path — `async/poll.spl` (2026-08-22)

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
