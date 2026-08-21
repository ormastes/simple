# Defect class: copy-on-write + accidental aliasing = O(n) per write

**Date:** 2026-08-21
**Status:** two seed-side fixes landed; static ratchet landed with 79 offenders baselined
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

## Open

* The 79 baselined `.spl` offenders are not yet fixed; MIR lowering (31) is the
  largest cluster and the next phase stage1 will reach.
* Per-Simple-function attribution in `perf_counters.rs` (top-30 by elements
  cloned) is not landed — the mechanism tests proved the specific defects without
  it, but the census still wants it.
* The JIT lane's collection representation has not been audited for the same
  class.
