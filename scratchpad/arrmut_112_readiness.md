# #112 array-mutation fix — redeploy readiness audit (read-only)

Date: 2026-07-12
Banked commit: `/tmp/wt_arrmut` HEAD `7b025f364dd44c3d299838cab5ae7826cb3f85bc`
Patch: `/tmp/arrmut.patch` (31 files, 1620 lines, generated via
`git -C /tmp/wt_arrmut diff 7b025f364dd~1 7b025f364dd`)

## Fix summary
Rust seed tree-walking interpreter stored every `Value::Object` (struct AND
class) as `Arc<HashMap<String, Value>>` mutated via copy-on-write
(`Arc::make_mut`). That gives value semantics unconditionally, so
`var c = arr[0]; c.val = 777` clones the Arc on bind (refcount 2) and the
field write privately copies instead of mutating the shared map — correct
for structs, wrong for classes (need reference semantics).

Root cause: `src/compiler_rust/compiler/src/interpreter/node_exec.rs` field
assignment called `Arc::make_mut(&mut fields).insert(..)` uniformly for
both struct and class instances.

Fix: new `ObjectFields` enum in `src/compiler_rust/compiler/src/value.rs`:
`Owned(Arc<HashMap>)` (existing COW) for structs/synthetic objects,
`Shared(Arc<Mutex<HashMap>>)` (real shared mutation) for classes. Object
construction sites pick storage kind via `ObjectFields::new_for_kind(..)`.
~90 call sites across 31 files updated mechanically to the new API
(interpreter/node_exec.rs, interpreter/expr/collections.rs,
interpreter_call/core/class_instantiation.rs, value_bridge.rs,
value_pointers.rs, etc.). Verified against the checked-in
`test/03_system/interpreter/interp_value_semantics_b35_spec.spl` — Task 112
class-in-array case now passes, Task 35B struct-value-semantics cases still
pass (no regression). Explicitly out of scope: a separate, pre-existing
JIT/Cranelift alias-leak for standalone `fn main()` scripts (not touched by
this fix — BDD specs always run through the interpreter, not JIT).

## Apply check — APPLIES CLEANLY
Current repo HEAD (`0097ce776296d5c1664de504a42d7c4b9b44e2d0`) is already
identical to `origin/main` FETCH_HEAD (`999372e8e6ed2cd85f0c4dbeac8f46bdaa2c0bdb`
at fetch time resolved to the same tip as local HEAD — no divergence).
`git apply --check --3way /tmp/arrmut.patch` reported "Applied patch to
'<file>' cleanly" for all 31 files, zero conflicts.

## Superseded check — NOT SUPERSEDED, bug still present
Grepped origin's current `value.rs`, `interpreter/node_exec.rs`, and
`interpreter/expr/collections.rs` for the fix's distinctive markers
(`ObjectFields`, `Owned(Arc`, `Shared(Arc<Mutex`): zero matches in all three
files. `node_exec.rs` still contains the uniform
`Arc::make_mut(&mut fields).insert(...)` pattern at ~20 call sites with no
struct/class distinction. The root-cause bug is unpatched on origin/main.

## Verdict: READY TO FOLD into next seed redeploy
- Patch applies cleanly against current origin/main tip (no conflicts, no
  rebase needed).
- Fix is not superseded — the COW-uniform bug it targets is still live in
  origin's interpreter.
- This is a Rust-seed-only change (bootstrap tool); it has zero effect on
  the currently-deployed `bin/simple` self-hosted binary until the seed is
  rebuilt and redeployed. No action taken here beyond verification — no
  edit/commit/build performed per read-only mandate.
