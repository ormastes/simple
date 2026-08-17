# A naked `case StructName(field):` pattern matched against an `Option<StructName>` value always falls to the wildcard arm

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
**Found:** 2026-07-29 (lane SYM0 `get-symbol-id-zero-nil`), while diagnosing
`doc/08_tracking/bug/hir_get_symbol_id_zero_returns_nil_2026-07-29.md`
**Area:** interpreter/runtime pattern matching (exact engine boundary not
isolated further — reproduced under `bin/simple test`'s default execution
path)
**Severity:** medium — silent wrong-answer (falls to `case _:`/wildcard, no
crash, no diagnostic), not scoped to any one value

## Finding

Given:

```simple
struct PId:
    id: i64

fn find(label: text) -> PId?:
    val found = self.names.get(label)
    if found != nil:
        val direct: i64 = self.names[label]
        return PId(id: direct)
    nil

fn get_item(id: PId?) -> Probe?:
    match id:
        case PId(raw):        # <-- naked constructor pattern, no Some() wrapper
            ...
        case _:
            nil
```

`match id: case PId(raw): ... case _: ...` **always** takes the `case _:`
branch when `id` is an `Option<PId>` value returned from a `return`-based
helper like `find` above — reproduced for **both** `raw=0` and `raw=1` in an
isolated probe (not an id-0-specific sentinel collision). `id.?` on the same
value correctly reports it present (`PId(id: 0)`, `PId(id: 1)`), so the
Option's own truthiness/payload-access path disagrees with what the
match-arm's implicit destructure-through-Option path sees.

The fix is **not** to fix the naked pattern generically — it is to always
write the safe, already-idiomatic form used throughout the codebase:

```simple
match id:
    case Some(PId(raw)):
        ...
    case nil:
        ...
```

This shape matched correctly for both `raw=0` and `raw=1` in the same probe.

## Confirmed site (fixed)

`src/compiler/20.hir/hir_types.spl` `SymbolTable.get_symbol(id: SymbolId?)`
had exactly this naked-pattern shape and was fixed in lane SYM0 (see
`hir_get_symbol_id_zero_returns_nil_2026-07-29.md`).

## Scope not covered

No repo-wide sweep for other `match <Option-typed-value>: case <StructOrEnum-with-payload>(...):`
(missing `Some(...)` wrapper) call sites was done — lane SYM0's mandate was
the one filed bug plus its named regressions. Any other such site would
silently misbehave the same way. A grep starting point: search for
`fn \w+\(.*: \w+\?\)` parameters immediately followed by a `match` whose
first non-wildcard `case` names a bare constructor (not `Some(...)`/`nil`).

## Isolated repro

See the probe embedded in the resolution note of
`hir_get_symbol_id_zero_returns_nil_2026-07-29.md`; reproduced via
`bin/simple test` against a scratch spec exercising a minimal `PTable`/`PId`
pair with the exact `find()` + naked-match shape above.

## Repo-wide sweep result (2026-07-30, lane NPS1)

Heuristic scan of all of `src/compiler` for the class: Optional-typed
params/locals/fields (56 match sites), calls to `?`-returning fns as
scrutinees (150 sites, incl. multi-line signatures), `.get/.lookup/.find/
.pop/.first/.last/.peek` call-scrutinees (32), and `expr[index]` scrutinees
(46 — all class (a): `[]` returns `T` directly, only `.get()` is
Option-returning). **Zero additional live defects** — the `hir_types.spl`
get_symbol site (fixed above) was the only instance. Residual blind spot:
multi-step chained scrutinees (`match a.b().c:`) aren't regex-enumerable;
spot checks of the densest files found nothing.

Lint rule honestly skipped: `match_exhaustiveness.spl` returns early on
`has_wildcard` (the buggy shape always has `case _:`) and has no resolved
types; `sffi_lint.spl` has `HirTypeKind.Optional` info but no function-body
walker. A real rule needs a new HIR body walker with type-environment
threading — filed as future work, not a drop-in addition.
