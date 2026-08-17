# `if val Some(x) = opt: EXPR else: EXPR2` loses field access on `x` when used as a value-producing expression (2026-07-31)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
(`src/lib/gc_async_mut/game2d/tilemap.spl::_pixels_for_tile`), not fixed at
the interpreter level.

**Impact:** any `val y = if val Some(x) = opt: x.field else: default` — i.e.
the pattern-binding `if` used as an *expression* whose "then" branch reads a
field off the bound variable — silently misbehaves under `bin/simple test`
(tree-walk interpreter). The exact same pattern used as a **statement**
(`if val Some(x) = opt: return x.field` / no value binding) works correctly.
This looks like exactly the shape used in production at
`src/lib/common/js/engine/jit.spl:112` (`val base_ir = if val Some(func) =
existing: func.ir else: ...`) — not independently confirmed broken there,
but the shape is identical and worth re-checking if that code path is ever
covered by a real assertion.

## Minimal reproducer

```simple
use std.spec

class Inner:
    width: i32

fn pick(tex: Inner?, default_w: i32) -> i32:
    val w: i32 = if val Some(t) = tex:
        t.width
    else:
        default_w
    w

fn pick_stmt(tex: Inner?, default_w: i32) -> i32:
    if val Some(t) = tex:
        return t.width
    default_w

describe "if-val-Some expression-form field access":
    it "expression form, Some":                  # FAILS
        expect(pick(Some(Inner(width: 42)), 7)).to_equal(42)
        # semantic: undefined field 'width': cannot access field on value of type 'symbol'

    it "statement form, Some":                    # PASSES
        expect(pick_stmt(Some(Inner(width: 42)), 7)).to_equal(42)
```

The error text ("cannot access field on value of type 'symbol'") suggests the
bound variable in the expression-form's "then" branch still holds the
`Option` variant tag/symbol representation instead of the unwrapped inner
value — a narrower failure than the `Option` type generally, since the
**statement** form correctly unwraps in the identical scenario.

## Workaround adopted

Rewrote the value-producing use as an early-return helper (statement form)
instead of an inline `if`-expression bound to a `val`:

```simple
fn _pixels_for_tile(tex: RegisteredTexture?, idx: i32, tw: i32, th: i32) -> [u32]:
    if val Some(t) = tex:
        return tilemap_sample_tile(t, idx, tw, th)
    _placeholder_tile_pixels(idx, tw, th)
```

Verified via `test/01_unit/lib/gc_async_mut/game2d/texture_registry_spec.spl`
(8/8 passing, exercising both the `Some` and `None` cases through a real
`Engine2D` render).

## Not fixed

The interpreter's expression-form binding itself was not touched — that is
core parser/interpreter code, out of scope for this lane's shortest-diff
budget. Filing this so the pattern is not silently reintroduced elsewhere and
so `jit.spl`'s use of the same shape gets re-audited once it has real test
coverage.

## Re-verification (2026-08-09)

Reproduced fresh against the currently deployed binary
(`bin/simple run`, tree-walk interpreter path — this binary identifies
itself as the Rust bootstrap seed). The minimal repro from this doc still
fails identically:
```
error: semantic: undefined field 'width': cannot access field on value of
type 'symbol'
```
The root cause lives in the semantic-analysis/interpreter binding logic for
the expression-form `if val Some(x) = opt: EXPR else: EXPR2`, which per repo
provenance is the Rust seed (`src/compiler_rust/**`), not `.spl` product
source — out of scope for this lane per repo rules (`feedback_fix_spl_not_rust`,
no seed edits, no bootstrap rebuild). Status confirmed unchanged:
**OPEN / ARCHITECTURAL** — genuinely reproducible, root cause outside
pure-Simple scope, workaround already in place at the one call site that
needed it.

## Re-investigated 2026-08-10 (independent verification, not a blanket claim)

Verified this doc's classification directly against source rather than
trusting the Status line: `/usr/bin/grep -rn "cannot access field on value of
type" src/compiler_rust/` hits exactly one place —
`src/compiler_rust/compiler/src/interpreter/expr/calls.rs:1002`, the format
string `"undefined field '{}': cannot access field on value of type '{}'"`,
matching this doc's exact reproduced error text. `/usr/bin/grep -rln "cannot
access field on value of type" src/compiler/` (the pure-Simple
`95.interp/*.spl` tree included) returns **zero hits** — there is no
editable `.spl` counterpart implementing this error path; the only code that
produces it is the Rust seed's expression-form `if val` binding logic cited
above, which is off-limits per repo rules (no `src/compiler_rust/**` edits
without explicit approval). Confirmed current `bin/simple` is the Rust seed
(`readlink -f bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`,
seed warning banner via `bin/simple --version`), so every reproduction in
this doc, including this one, exercised the seed's interpreter. Status
confirmed unchanged: **OPEN — ARCHITECTURAL (Rust seed interpreter
`interpreter/expr/calls.rs:1002`, verified 2026-08-10)**.
