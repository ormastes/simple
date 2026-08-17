# Assigning to a scalar field of a `class` fails native/AOT MIR lowering

> **STATUS 2026-08-10 (later): FIXED — and the title above is a MIS-ATTRIBUTION.**
> The trigger is not `class`, not a field, and not the assignment. It is the
> **suffixed integer literal** `1i64` on the right-hand side. Root cause and the
> one-line fix are in "Resolution" at the bottom; read that first — everything
> above it is the original filing and is now historical.

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
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

---

## Resolution (2026-08-10)

### The bisection was right about the DATA and wrong about the CAUSE

All six probes were re-run at origin `275d6466cd2` in a pinned pristine tree and
reproduced the filed table exactly (`hello`/`n3`/`n6` build, `n5`/`n2`/`n4` fail
with `merge`x4). So the table is sound. The *inference* from it is not.

Every failing probe writes `c.n = c.n + 1i64`; every passing one does not write
`x = x + <suffixed literal>` at all. `class`, `field`, and `assignment` are
**confounds** — they co-vary with the real trigger across all six rows.

The discriminating experiment is a one-character A/B (`n7.spl` = `n5.spl` with
`1i64` -> `1`), holding the class, the field, and the assignment fixed:

| probe | assignment | native-build |
|---|---|---|
| `n5.spl` | `c.n = c.n + 1i64` | **FAIL** `merge` |
| `n7.spl` | `c.n = c.n + 1` | **PASS** |

Same class, same scalar field, same assignment. Only the literal suffix differs.

### Root cause — a missing tag in an AST-level gate

`src/compiler/10.frontend/desugar/collection_desugar.spl:138` —
`is_definite_scalar_addend`. Pattern B of the collection desugar rewrites
`x = x + rhs` into `x.merge(rhs)`, gated on the addend's *syntactic shape*
because the pass runs before type-checking. The gate listed `EXPR_INT_LIT` and
`EXPR_FLOAT_LIT` but **not `EXPR_SUFFIXED_LIT`**, which is a distinct arena tag
(`_AstExpr/nodes.spl:53`) carrying `1i64` / `2u8` / `1.5f32`.

So `c.n = c.n + 1i64` failed the scalar gate, was rewritten to
`c.n.merge(1i64)`, and `merge` has no MIR lowering — hence
`unresolved method call: merge`. Confirmed directly by a probe at the error site
(`method_calls_literals.spl`), which printed
`[q25-probe] unresolved method=merge args=1 fns=[bump, cnew, main]`: the
synthetic `merge` is manufactured while lowering the probe's OWN `bump`, a
function whose source contains no `.merge` at all.

This also explains why it read as native-only: the desugar runs for every lane,
but only the native lane needs a MIR lowering for `merge`; the interpreter and
JIT resolve it as array concatenation at runtime and silently do the wrong thing
only if the receiver really is a collection.

### Fix

One tag added to the gate (plus the comment explaining why):
`EXPR_SUFFIXED_LIT`. `EXPR_CAST` was considered and deliberately excluded —
`x as [i64]` casts to a collection, so gating on it would suppress a legitimate
rewrite.

### Verification

- `n5.spl` native-build at origin+fix: `rc=0`, binary produced, the error-site
  probe never fires (`merge=0`).
- Regression oracle: `test/01_unit/compiler/frontend/collection_desugar_gate_spec.spl`
  gains a suffixed-literal example -> `Results: 4 total, 4 passed, 0 failed`.
- **Revert-proof:** removing the one-line fix turns that example RED with
  `expected 1 to equal 0` -> `Results: 4 total, 3 passed, 1 failed` (exit 1).
- **Negative control:** the sibling example `xs = xs + [2]` must still rewrite
  (`rewrite_count()==1`) and passes in BOTH the fixed and reverted runs — so a
  gate that suppressed every rewrite would be caught rather than scored green.

### Still open, and NOT caused by this fix

The rebuilt `n5` binary builds and exits 0 but **prints nothing**, where the
interpreter prints `N5=1,2`. This is pre-existing and independent: the
**origin-built `n3` and `n6` binaries — built before any edit — also print
nothing**, while `hello.spl` (a non-interpolated `print`) prints correctly. So
interpolated `print` with an embedded call is silently dropped in native
binaries, and the original table's `PASS` rows were build-success-only and never
checked output. Filed separately as
`native_interpolated_print_with_call_silently_drops_output_2026-08-10.md`.
