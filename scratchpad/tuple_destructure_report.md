# Tuple Destructure on Native --entry Path (bug #169 cluster) — Report

Worktree base: `0b63b447263` ("fix: harden pure native runtime ABI").
Oracle: `env -u SIMPLE_BOOTSTRAP bin/simple run p.spl`.
Native: `env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry p.spl -o out --clean && ./out`.

## Verdict

`val (a, b) = (literal tuple)` now works on the native `--entry` build path.
Non-literal initializers fail the build loudly with a clear, dedicated error
(exit != 0, no binary emitted). Smoke matrix gate met: 14/15 pass,
0 codegen_fallback_hits, only fail = `option_nil_check` (the allowed one).

## Root cause found (differs from the assumed one)

The failure was NOT primarily a missing HIR desugar. The parser's
`parse_tuple_destructure_val` / `..._var` (src/compiler/10.frontend/core/
parser_stmts.spl) corrupted **every plain-identifier destructure name** to the
literal string `"Ident"`: `tok_kind_name(TOK_IDENT) == "Ident"` and
`keyword_lookup("Ident") == TOK_IDENT` (the not-a-keyword fallback), so the
"keyword-as-name" round-trip check was trivially true for every identifier.
This is the exact bug class already fixed for single-name `val` in
`parse_val_decl_stmt` (the G26 comment there describes it); the fix never
propagated to the parenthesized tuple form. So HIR received
`val ("Ident,Ident") = ...` and the real names `a`/`b` were never defined →
"unresolved name: a/b". Fixed by adding an explicit `TOK_IDENT` branch (capture
`par_text_get()` first) in `parse_tuple_destructure_val`, mirroring the
existing single-name fix. (`parse_tuple_destructure_var` has the same bug; left
untouched — `var (...)` destructure is out of this task's scope.)

On top of that, the scoped HIR desugar was implemented as specified:
`lower_hir_stmt_multi` detects the parser's `"(a,b)"` joined-name encoding of
`StmtKind.Val` and, when the initializer is `ExprKind.TupleLit`, expands it
into N ordinary `HirStmtKind.Let` bindings (elements lowered once, left to
right). Any other initializer emits a fatal error.

## Battery (oracle vs native)

All programs start with `print(0)` to sidestep a PRE-EXISTING native-path bug
unrelated to this change (see Deviations #1).

| Program | Oracle stdout (lines) | Native stdout | Native build/run exit | Match |
|---|---|---|---|---|
| b1: `val (a,b) = (1,2)` (2-elem int) | 0,1,2 | `012` | 0 / 0 | YES (see Dev.#2 newline note) |
| b2: `val (x,y,z) = (10,"hello",30)` (3-elem int+string) | 0,10,hello,30 | `010hello30` | 0 / 1 | YES values; run-exit 1 is pre-existing (Dev.#3) |
| b3: `val (a,b) = (add_one(1), 2+3)` (exprs as elements) | 0,2,5 | `025` | 0 / 0 | YES |
| b4: 3 destructures in one main + arithmetic mixing bound names (`(a,b)=(1,2)`, `(c,d,e)=(a+b,100,7)`, `(sum1,sum2)=(a+c,d+e)`) | 0,1,2,3,100,7,4,107 | `012310074107` | 0 / 0 | YES |
| b6: keyword-ish name `val (type, count) = (1,2)` | 0,1,2 | `012` | 0 / 0 | YES |

### Negative tests (loud-fail verified)

| Program | Expected | Result |
|---|---|---|
| b5: `val (a,b) = pair` (variable init, names used) | build fails, no binary | exit 1, no binary, error: `unresolved name: tuple destructure `val (a,b) = ...` requires a literal tuple initializer, e.g. `val (a, b) = (x, y)`; a non-literal initializer (variable, function call, ...) is not supported` |
| b5b: same but names never used afterwards | build fails, no binary | exit 1, no binary, same clear error |

Loudness note: driver.spl's `_hir_lowering_error_is_fatal` only promotes HIR
errors starting with `"unresolved name:"` to fatal; everything else is
silently downgraded to a warning. The destructure errors therefore carry that
prefix deliberately (commented in code). Verified empirically: without the
prefix the message vanished entirely (build still failed via downstream
`unsupported MIR expression: HirExprKind::Error`, which is in the MIR fatal
allowlist — but the clear message never surfaced).

## Smoke matrix

Run 1 (before final error-message wording, functionally identical code):

```
total=15 pass=14 fail=1 xfail=0 xpass=0 codegen_fallback_hits=0
```

Only fail = `option_nil_check` (rc got=1 want=7) — the allowed failure.
Gate (>=14/15, 0 fallback hits, only option_nil_check failing): **MET**.
Run 2 on the FINAL code state (after the loud-error message prefix change):

```
total=15 pass=14 fail=1 xfail=0 xpass=0 codegen_fallback_hits=0
[option_nil_check] (14) Option/nil check (x.?) -> FAIL (rc got=1 want=7, fallback_hits=0)
```

Gate (>=14/15, 0 fallback hits, only option_nil_check failing): **MET on both runs**.

## Files touched

- `src/compiler/10.frontend/core/parser_stmts.spl` — `parse_tuple_destructure_val`: explicit `TOK_IDENT` branch (first element + loop), fixing the every-identifier→"Ident" corruption.
- `src/compiler/20.hir/hir_lowering/statements.spl` — new `lower_hir_stmt_multi` + `lower_hir_tuple_destructure_val` (literal-tuple desugar into N `Let`s; fatal errors for non-literal init and arity mismatch).
- `src/compiler/20.hir/hir_lowering/expressions.spl` — `lower_hir_block` and `lower_hir_block_unit` (both branches) iterate via `lower_hir_stmt_multi` and splice; tail-value extraction applies to the last lowered stmt of the last source stmt.

## Names corrupted by the tokens.spl keyword_lookup round-trip bug (tokens.spl:435)

- Before the parser fix: **ALL plain identifiers** were corrupted (to "Ident") — that was the primary bug, now fixed for `val (...)`.
- After the fix, names that ARE real keywords still round-trip through the keyword branch. `type`, `count` verified working. `val` as a destructure name diverges: oracle rejects it (`semantic: variable `val` not found`) while native accepts it — pre-existing keyword-name edge, out of scope; avoid keyword names.
- `var (...)` destructure still has the "Ident" corruption (untouched, out of scope).

## Deviations / pre-existing bugs observed (NOT caused by this change; verified on unmodified tree via `git stash`)

1. **First-statement `val` binding loses its value on native --entry**: `fn main(): val a = 11; print(a)` prints `0`. Control `val a=11; val b=22; print(a); print(99); print(b)` → `09922` on the UNMODIFIED worktree. Any statement before the first `val` (e.g. `print(0)`) avoids it. Battery programs prepend `print(0)` for this reason.
2. **Native `print()` emits no trailing newline** while the oracle interpreter does. Control (no destructure): oracle `5\n7\n` vs native `57`. Oracle equality is therefore evaluated on the printed values/order, which match exactly in every battery case.
3. **Native binaries that print strings exit 1**: control `print("hello")`-containing program without any destructure also exits 1 (b2 inherits this).

## Test artifacts

Battery programs/logs lived in the (now removed) worktree at `scratch/battery/`;
programs are reproduced inline in the table above.
