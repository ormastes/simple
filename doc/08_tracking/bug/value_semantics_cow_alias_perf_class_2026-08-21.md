# Defect class: copy-on-write + accidental aliasing = O(n) per write

**Date:** 2026-08-21
**Status:** two seed-side fixes landed; static ratchet landed with 79 offenders baselined, remediated to 23, then to 7 (zero KEYSINLOOP) on 2026-08-21
**Scope:** whole compiler — HIR import registration, MIR lowering, mono, driver module tables

## What the class is

Simple has **value semantics**. The interpreter implements them as
**copy-on-write**: a collection is an `Arc`-backed container (`Value::Array(Arc<Vec<..>>)`,
`Value::Dict(Arc<HashMap<..>>)`, `Value::Object { fields: Arc<HashMap<..>> }`) and every
mutation goes through `Arc::make_mut`. When the `Arc` is **uniquely owned** that mutates
in place, O(1) amortized. When the `Arc` is **aliased** (`strong_count > 1`) it
`clone()`s the entire container first — which is exactly right, because two live
bindings must not observe each other's writes.

The defect is not COW. The defect is **accidental aliasing**: code (or the
interpreter's own bookkeeping) holds a second reference to a collection across a
write, when there was never a second live binding to preserve. Then the "isolate
the alias" copy fires on *every single write*, and building an n-element
collection costs O(n²).

Four shapes produce it:

| shape | example | why it aliases |
|---|---|---|
| **(a) round trip through a local** | `val t = self.table` … `t.push(x)` … `self.table = t` | the field and the local hold the same Arc across the write |
| **(b) by-value helper** | `self.xs = push_into(self.xs, v)` | the field still holds the Arc while the parameter binding holds it too |
| **(c) materialized view in a loop** | `.keys()` / `.values()` inside a `while`/`for` body | a fresh vector of every key per iteration |
| **(d) interpreter-created temporary** | `self.xs.push(v)` routed through a place path that copies the field into a temp | the temp is the alias; the source code is innocent |

Shape (d) is the nastiest, because the `.spl` source looks correct. It was the
one measured here.

## Why fixtures hide it

The cost is `O(size of the collection)` per write and **zero at size zero**. A
unit fixture with a 5-element table copies 5 pointers per write — nanoseconds,
lost in noise, and the asymptote is invisible because there is only one data
point. The same code on the 667-module closure copies tens of thousands of
entries per write. Concretely, HIR register calls went **1.7 ms → 15.8 ms** as
the module table grew — a 9x slowdown produced by *no code change at all*, only
by the table getting bigger. Nothing in a green test run distinguishes O(1) from
O(n) per write.

That is why the detectors below count **operations, not time**: a buffer-identity
count is deterministic, size-independent, and fails loudly on a loaded box, where
a wall-clock threshold would be flaky.

## How the detectors expose it

### Runtime: buffer-identity mechanism tests

`Arc::make_mut` on a uniquely-owned `Arc` reuses the backing buffer; on an
aliased one it allocates a new one. So **counting distinct backing-buffer
addresses across N mutations** separates the two exactly:

* sole owner → O(log N) distinct buffers (amortized `Vec` growth only)
* aliased per write → ~N distinct buffers

Measured on a 2,000-push loop through `handle_method_call_with_self_update`:

| shape | distinct buffers, pre-fix | post-fix |
|---|---|---|
| `xs.push(v)` (identifier receiver) | 3 | 3 |
| `o.xs.push(v)` (field receiver) | **1321** | **< 64** |

The identifier shape was already correct. The field shape — the shape every
struct-field accumulator in the compiler uses — was copying the whole array on
essentially every write.

### Static: `scripts/check/check-cow-alias-hotpath.shs`

A fail-closed ratchet over `src/compiler/**.spl` for the textual shapes (a), (b)
and (c). Verdict is the last stdout line; a 0-file scan is `ERROR`, never a pass;
`--selftest` runs first and is fatal (6 fixtures, including one proving a
take/store-back pair split across two functions does **not** pair up into a false
offender). Current measurement:

```
PASS — 1808 file(s) scanned, 79 offender(s) checked, 0 new, 0 stale
```

Offenders are frozen in `scripts/check/cow_alias_hotpath_baseline.txt`. A new one
FAILs; a baselined one that disappeared is a **stale baseline** and also FAILs,
because a baseline that no longer describes the tree is how a ratchet silently
stops ratcheting.

The 79 confirm the class is not confined to HIR import registration:

| area | offenders |
|---|---|
| `50.mir` (MIR lowering) | 31 |
| `80.driver` | 8 |
| `20.hir` | 6 |
| `40.mono` | 5 |
| `00.common/di` | 5 |
| `10.frontend` | 4 |
| rest | 20 |

By kind: 46 ROUNDTRIP, 21 BYVALUE, 12 KEYSINLOOP.

## Fixes landed

### 1. `obj.field.push(x)` mutated an aliased array — shape (d)

`handle_method_call_with_self_update` routed `o.xs.push(v)` to the general PLACE
receiver path, which resolves the place by **copying the field into a temp**,
mutating the copy and rebuilding the root. `interpreter/expr/calls.rs` already had
the correct ownership-gated fast path (`try_field_array_mutation_in_place`) but it
sits **downstream** and was unreachable for any statement routed through
`handle_method_call_with_self_update` — a bare expression statement, a
`val x = obj.f.pop()` initializer, a loop body.

The fix reuses that same helper from the upstream site, so there is one kernel and
no new semantics. Pre/post: **1321 → <64 distinct buffers per 2,000 pushes.**

### 2. Nested assignment targets rejected — the cause of shape (a)

The index-assignment path hand-wrote exactly two shapes (`ident[i] = v`,
`ident.field[i] = v`) and rejected anything deeper with
`invalid assignment: complex field access not supported`. That is a grammar hole
with a performance cost: the workaround it **forces** is precisely shape (a),

```
var row = self.rows[i]
row.cols[k] = v
self.rows[i] = row
```

whose intermediate binding aliases the inner container. `SymbolTable.define` pays
exactly this.

`interpreter/place.rs` already models a place as a root variable plus an arbitrary
projection chain and walks it with `Arc::make_mut`, and the FIELD-target branch
already fell back to it. The fix gives the INDEX-target branch the same fallback.
`self.a[i].b[k] = v` now lands in place. The JIT lane already accepted this shape,
so this also closes an engine divergence rather than opening one.

## Semantics are preserved

Both fixes are **unobservable** by construction: they only remove copies the
program could never have observed, because the second reference was the
interpreter's own temporary. A genuinely live alias still copies. Pinned by four
tests that would fail if COW were weakened:

* a live alias of a local array still copies on write and stays unchanged
* a live alias of a **field** array likewise
* a live alias of an **intermediate** container in a nested assignment does not
  observe the nested write
* `pop` still returns the element, not the array

`cargo test -p simple-compiler --release --lib`: **3765 passed / 52 failed**,
byte-identical to the pre-change 52 baseline.

## Rule for new code

Recorded in `.claude/rules/code-style.md`:

> Never mutate a collection through a temporary alias. Mutate through the single
> owner (`self.table.push(x)`, `self.a[i].b[k] = v`) and hoist `.keys()` above the
> loop. Ratcheted by `sh scripts/check/check-cow-alias-hotpath.shs`.

## Offender remediation, 2026-08-21 (79 -> 23)

Every ROUNDTRIP and every mechanically-safe BYVALUE offender was rewritten to
write through the owning field. Each rewrite is semantics-identical: the
temporary was never read after the mutation, so collapsing the read-modify-write
into a direct in-place write cannot be observed.

| layer | file(s) | ROUNDTRIP | BYVALUE | how |
|---|---|---:|---:|---|
| 00.common | `di.spl` | 5 | — | `self.bindings[name] = factory`, `self.singletons[name] = v`, `self.all_bindings.push(...)` |
| 25.traits | `trait_solver.spl` | 2 | — | write `self.traits` / `self.trait_methods` directly; only the small per-method owner list is touched |
| 40.mono | `instantiation.spl` | — | 5 | `_template_remove_text(self.in_progress, k)` -> `me _drop_in_progress(k)` rebuilding into a fresh unaliased list |
| 50.mir | `mir_lowering_types.spl` | 11 | — | `bind_local`, `remember_local_hir_type`, `copy_local_hir_type_metadata`, `mark_runtime_value_local` write the aligned local arrays in place |
| 50.mir | `_MirLowering/module_lowering.spl` | 16 | — | enum registry dicts written directly; `reindex_enum_variant_owners` mutates `self.enum_variant_owners` |
| 50.mir | `mir_lowering_stmts.spl`, `_MirLowering/function_lowering.spl` | 4 | — | `self.resource_owned_locals.push(local)` |
| 70.backend | `svmg_lowering.spl` | 2 | — | `self.code.push(...)` / `self.code[i] = ...` in `emit_u8` and `patch_rel16` |
| 70.backend | `linker/lazy_instantiator.spl` | — | 1 | `lazyinstantiator_drop_in_progress(self, sym)` |
| 80.driver | `driver_types.spl` | 6 | — | storage-registry rows pushed through the owning fields |
| 80.driver | `incremental.spl` | — | 2 | `add_edge(self.dependencies, ...)` helper deleted; `add_dependency` touches only the per-key list, never a copy of the whole edge dict |
| 99.loader | `jit_instantiator.spl` | — | 2 | `me _drop_in_progress(name)` |
| **total** | | **46** | **10** | |

Guard after: `PASS — 1808 file(s) scanned, 23 offender(s) checked, 0 new, 0 stale`.

`test/01_unit/compiler/driver/native_build_jit_ambiguity_source_spec.spl` pins
the `in_progress` shapes as source text; its three affected assertions were
updated to the new owner-method form and now also assert the old
take-and-return helpers are gone. Its `in_progress: [text]` / no-`Set<text>`
intent is unchanged, and all four of its `in_progress` examples pass.

### What was deliberately NOT changed

The 12 remaining KEYSINLOOP entries are not hoistable. In
`20.hir/.../_Items/module_lowering.spl` (7 of them) each `.keys()` call is over a
*different* dict — one per module surface per declaration kind — and each result
is consumed once, so there is no repeated materialization of the same key set to
lift out. Hoisting is not available because the tree has no dict-direct iteration
idiom; `.keys()` is the only way to walk a dict. They stay baselined so the
ratchet keeps blocking genuinely new ones. The 11 remaining BYVALUE entries
(`00.common/effects.spl`, `10.frontend/treesitter/outline.spl`,
`60.mir_opt/**`, `70.backend/linker/link.spl`,
`99.loader/loader/module_loader.spl`) are on cold link/unload/outline paths;
several are additionally pinned as source text by the spec above and want their
own reviewed change.

### Counter measurement: attempted, not obtained

`SIMPLE_PERF_COUNTERS=1` on a 3-module fixture through
`src/app/cli/bootstrap_main.spl compile` reports **1099 clones / 1348 elements,
byte-identical before and after** — because that pipeline aborts inside HIR
(`error[E1002]: function 'module_surface_name_position' not found`, an unrelated
in-flight change in the shared working tree) and never reaches the MIR, driver
or DI code that was edited. The measurement is therefore non-discriminating
rather than a null result, and no clone-reduction figure is claimed here. It
should be re-run once the HIR path builds again.

## KEYSINLOOP resolved, 2026-08-21 (23 -> 7, zero KEYSINLOOP)

### Is there dict iteration that does not materialize keys?

The premise behind holding the 12 KEYSINLOOP offenders was "the tree has no
dict-direct iteration idiom". That is half right, and the half that is wrong
changes the answer.

`for (k, v) in d:` **does exist and does work.** `interpreter_control.rs:3410`
detects a `Value::Dict` iterable and suppresses `auto_enumerate` precisely
because dict items are already `(key, value)` tuples, and both it and `.keys()`
go through `dict_entries_sorted`, so the two agree on order **exactly** —
verified by running both loops over the same dict and diffing the sequence.
(A stale comment at `25.traits/trait_coherence.spl:91` claimed "for (k,v) in
dict is broken in compiled mode"; it is no longer true of the interpreter lane.)

But it is **not cheaper**, which is the part that matters here:

| path | what it allocates |
|---|---|
| `d.keys()` (interpreter) | a `Vec` of every key |
| `for (k, v) in d` (interpreter) | `iter_to_vec` -> a `Vec` of every `(k, v)` **tuple** |
| native / JIT | `rt_dict_keys`, `rt_dict_values`, `rt_dict_entries` — the only three the runtime exposes, **all materializing** |

There is no cursor, view, or lazy iterator anywhere in the interpreter or the
runtime. So rewriting a `.keys()` loop into a `(k, v)` loop allocates *strictly
more*, not less. Adding a real non-materializing iterator would mean a new
runtime cursor ABI plus interpreter, MIR and JIT lowering — and it would buy
nothing for the 12 sites, for the reason below.

### The 12 were mostly not offenders

Re-examined individually, **11 of the 12 had a receiver that is REBOUND on every
iteration** — `for surface in ...` then `surface.callables.keys()`,
`val module = mods[i]` then `module.structs.keys()`, `val impl_def = ...` then
`impl_def.methods.keys()`. Each of those materializes the keys of a *different*
dict, visits every key exactly once, and totals O(total entries). That is
optimal and not rewritable into anything cheaper. The O(n^2) the rule names was
never present at those sites; the detector simply did not distinguish a
loop-invariant receiver from a loop-varying one.

`scripts/check/check-cow-alias-hotpath.shs` now makes that distinction, and a
second, opposite defect was found while doing it: loop indents were kept in a
single scalar, so closing an INNER loop read as "no longer in a loop" while
still inside the OUTER body, hiding every offender that follows an inner loop.
Replaced with a stack. Net effect on the rule: **-11 false positives, +1 true
positive** the old rule structurally could not see.

### Fixed

| site | was | now |
|---|---|---|
| `25.traits/trait_coherence.spl:100` | `self.local_types.keys().len() > 0` in a doubly-nested loop | `.len() > 0` — no array built to ask "non-empty?" |
| `70.backend/backend/vulkan_backend.spl:264,271` | `push_arg_locals.keys().len() > 0` (found only by the stacked-indent fix) | `.len() > 0` |
| `70.backend/backend/native/regalloc.spl:160` | `intervals.keys()` re-materialized per back-edge | hoisted above the scan; the back-edge pass only rewrites values at existing keys, never adds one, so the key set is fixed |
| `10.frontend/treesitter/outline.spl` (4 BYVALUE) | `self.X = X_push(self.X, item)` | `self.X.push(item)`; the 3 helpers were bare `blocks.push(item)` and are deleted |

Baseline **23 -> 7**. Every surviving offender is a cold-path BYVALUE whose
helper does real work (dedupe, removal, stats folding) and is not a mechanical
rewrite.

### Mechanism test

`compiler/src/interpreter_method/collections.rs`,
`mod keys_materialization_tests` — a test-only thread-local counter incremented
where `.keys()`/`.values()` actually builds the array, driven through the real
`exec_for`:

* `.keys()` in the loop BODY, invariant receiver: **200 materializations for 200
  iterations** — the O(n^2) shape, asserted to still be there so the rule is not
  guarding a phantom.
* hoisted `.keys()` as the loop's iterable: **exactly 1**, i.e. **0 per
  iteration** — the property the rewrites bought.
* size-independence: still exactly 1 at 1, 8 and 512 entries, so the assertion is
  not an artifact of one dict size.

Counting materializations rather than wall time keeps this exact on a loaded box.
The counter is `#[cfg(test)]`, so the production dict path pays nothing.

## Open

* 7 baselined `.spl` offenders remain, all BYVALUE on cold paths; see
  "What was deliberately NOT changed" above for why each is held.
* No non-materializing dict iteration exists in either the interpreter or the
  runtime (`rt_dict_keys`/`values`/`entries` are the whole surface). Nothing in
  the compiler currently needs one — every remaining `.keys()` in a loop is over
  a loop-varying receiver — but a genuinely hot invariant-receiver site would
  have no cheap idiom to reach for.
* A discriminating runtime counter delta for the 56 fixed offenders has not been
  measured — the compile pipeline that reaches them is currently broken in HIR.
* Per-Simple-function attribution in `perf_counters.rs` (top-30 by elements
  cloned) is not landed — the mechanism tests proved the specific defects without
  it, but the census still wants it.
* The JIT lane's collection representation has not been audited for the same
  class.
