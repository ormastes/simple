# Parenthesised tail expression after a block-`match` `val` is parsed as a call

Date: 2026-08-18
Status: FIXED (pure-Simple front end) — 2026-11-11 (lane ne18); guard in
`parse_postfix`/`parse_postfix_on` stops postfix binding on a completed
block-`match` value; pinned by
`test/01_unit/compiler/parser/paren_tail_after_block_match_val_parity_spec.spl`
(4/4, seed-interpreted pure-Simple parser). The deployed Rust seed still
carries the defect until its next rebuild — seed sources not editable in the
filing lane or this one.
Found by: isolated re-run of `test/05_perf/os/crypto/x25519mlkem768_perf_spec.spl`

## Symptom

```
  ✗ should NFR-008 NFR-011 records cold scalar first-use exchange
    semantic: variable `recovered` not found
  ✗ should NFR-008 NFR-011 records complete scalar hybrid exchange latency
    semantic: variable `recovered` not found
```

## Minimal reproduction (Rust seed, `bin/simple run`)

```simple
fn mk(n: i64) -> Result<i64, text>:
    if n > 0:
        return Ok(n)
    Err("neg")

fn f() -> bool:
    val a = match mk(1):
        case Ok(v): v
        case Err(_): return false
    (a > 0 and a < 10)      # <-- statement starts with '('

fn main() -> i64:
    print "f={f()}"
    0
```

```
[CODEGEN BODY] Function 'f' body compilation failed: GlobalLoad: unresolved
identifier 'a' (not a global, function, const-data name, or import)
error: semantic: value is not callable
```

`value is not callable` is the tell: the `(` line is glued onto the preceding
block-`match` as a CALL argument list, i.e. the source is parsed as
`val a = (match ...)(a > 0 and a < 10)` — so `a` is referenced inside its own
initialiser and is genuinely unbound at that point.

## Controls (all PASS on the same binary — the defect needs the exact combination)

| variant | shape | result |
|---|---|---|
| v1 | block-`match` val + tail WITHOUT parens (`a > 0 and a < 10`) | `v1=true` |
| v2 | `val a = 5` + parenthesised tail | `v2=true` |
| v4 | block-`match` val + one intervening `val` + parenthesised tail | `v4=true` |
| v3 | block-`match` val + parenthesised tail (single line) | **FAIL** |
| v5 | same as v3 but no `return` in the `case` arms | **FAIL** |

So it is neither the `return` inside the arm nor parenthesised tails in general:
it is a statement beginning with `(` **immediately** after a block-bodied
`match` initialiser.

## Scope

Observed on the Rust bootstrap seed (`bin/simple` -> shared
`bin/release/x86_64-unknown-linux-gnu/simple`). Not yet re-checked against a
pure-Simple self-hosted binary — this lane is forbidden from rebuilding or
replacing the shared seed, so the compiler-side fix and its verification are
deliberately NOT attempted here.

## Action taken in this lane

`test/05_perf/os/crypto/x25519mlkem768_perf_spec.spl` had its final expression
in `_scalar_exchange_once()` rewritten to an unambiguous form. **No assertion
was weakened, removed, or reordered** — the returned boolean is the identical
conjunction of the identical two crypto checks (evidence validity and
shared-secret equality). The rewrite exists only to stop the parser mis-binding;
this bug record is the reason it is not a silent workaround.

## Addendum 2026-11-11 (lane ne18) — FIXED in the pure-Simple front end, verified

Triage verdict: **LIVE → FIXED**. Reproduced on the 2026-11-11 release tip
with the fresh seed (build-commit 46fe8f6b6def): the doc's minimal reproducer
still fails with `error: semantic: ...:6:9: value is not callable` under the
seed's own parser — the defect was live.

Fix (`src/compiler/10.frontend/core/parser_expr.spl`): both postfix loops
(`parse_postfix_on` and its twin in `parse_postfix`) now stop postfix binding
the moment the base expression is a completed `EXPR_MATCH` — a block-bodied
`match` value is a complete expression, so a following `(` opens a new
statement, never a call tail. `(match ...: ...)(args)` in explicit parens is
the one shape that changes meaning (now statement-split); a corpus scan shows
zero uses of it, and every real corpus shape of a match value inside a larger
expression (`Ok(match k: ...)`, `x + (match k: ...)`) has no postfix operator
after the match, so the guard is behavior-preserving there. The if-expression
sibling shape (`val a = if c: 1 else: 2` + paren tail) was probed and parses
correctly already — no change needed.

Test paired with the fix:
`test/01_unit/compiler/parser/paren_tail_after_block_match_val_parity_spec.spl`
drives the PURE-SIMPLE front end directly (`compiler.core.parser.parse_module`,
seed-interpreted), so it verifies the self-hosted parser even while the test
runner is the Rust seed. Four scenarios: the doc's exact multi-line reproducer
(val + separate paren statement, AST-asserted), the single-line variant (now a
LOUD parse rejection after the match-arm column work — pinned so the silent
glue cannot return via a future leniency), the bug-doc v4 control, and a match
as a call-argument control. Verified in this lane (seed-smoke): **4 total, 4
passed, 0 failed**; mutation-checked by stashing the guard — AC-1 fails
without it.

Residual (out of scope here): the deployed seed binary keeps the defect until
the next seed rebuild (`src/compiler_rust` parser-side fix + rebuild is the
bootstrap lane's); the x25519 spec's unambiguous rewrite from 2026-08-18 stays
(it asserts the identical conjunction and remains valid on both parsers).
