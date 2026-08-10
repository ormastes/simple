# Assigning to a scalar field of a `class` fails native/AOT MIR lowering

- **Status:** OPEN — native/AOT backend defect
- **Filed:** 2026-08-10
- **Severity:** blocks AOT for any `class` that carries mutable scalar state —
  i.e. for the entire "use a class when you need shared mutable state" pattern
  the repo already relies on (`notebook/lane_locks.spl`,
  `service/lease_manager.spl`).
- **Error:** `MIR error: MIR lowering error: unresolved method call: merge`

## Minimal reproduction

`build/q18/n5.spl` (7 lines, no imports):

```
class Counter:
    n: i64
fn cnew() -> Counter:
    Counter(n: 1i64)
fn bump(c: Counter) -> i64:
    val id = c.n
    c.n = c.n + 1i64
    id
fn main() -> i64:
    val c = cnew()
    print "N5={bump(c)},{bump(c)}"
    0i64
```

```
bin/simple native-build build/q18/n5.spl -o /tmp/n5      # exit 1
  [ERROR] MIR error: MIR lowering error: unresolved method call: merge
```

Runs correctly under the interpreter and the JIT (`1,2`).

## Bisected — it is the class scalar-field ASSIGNMENT, nothing else

Each row is a separate `native-build` of a self-contained file. `merge` is not
a symbol any of these programs mention.

| probe | shape | native-build |
|---|---|---|
| `build/q18/hello.spl` | `print` only — **positive control**, proves the lane works | **PASS** |
| `build/q18/n3.spl` | `class` + `static fn` + read-only `fn`, no mutation | **PASS** |
| `build/q18/n6.spl` | `class` with `[i64]` field, `b.items.push(v)` from a free fn | **PASS** |
| `build/q18/n5.spl` | `class` with `i64` field, `c.n = c.n + 1` from a free fn | **FAIL** `merge` |
| `build/q18/n2.spl` | same assignment inside a `me` method | **FAIL** `merge` |
| `build/q18/n4.spl` | scalar assignment + array push | **FAIL** `merge` |

So: declaring a class is fine, calling methods on it is fine, mutating a
*collection* field is fine. Assigning to a *scalar* field is what does not
lower — via a free `fn` or via a `me` method alike, so it is the assignment,
not the `me` marker.

The positive control matters: without `hello.spl` passing, every FAIL above
would be equally explained by "native-build is broken on this host".

## Consequence right now

`src/lib/nogc_sync_mut/service/lease_manager.spl` became a `class` (see
`struct_dict_field_mutation_engine_divergence_2026-08-10.md` and the commit
that fixed `_next_lease_id`) and assigns `self.next_id` and `self.leases`.
It is therefore **correct under the interpreter and the JIT — the two lanes
`bin/simple test` and `bin/simple run` actually use — and not AOT-compilable
until this is fixed.** That trade was taken deliberately rather than
open-coding a workaround (e.g. deriving the counter from an array length),
per the repo rule against silently normalising a workaround when a short,
safe form fails.

## Unblock condition

Native/AOT MIR lowering resolves scalar field assignment on a class receiver.
Then re-run the six probes above; all six must PASS, with `hello.spl` still
passing as the control.
