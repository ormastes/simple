# Two bare `_` placeholders in one string template: `variable __p1 not found`

- **Filed:** 2026-07-30
- **Severity:** medium — silently unusable feature shape (string template with
  a repeated bare placeholder), no known workaround inside the template
  itself
- **Status:** FIXED (lane TPL1, 2026-07-30) — root cause pinned down and
  patched in the Rust seed (`src/compiler_rust`), verified by 2 new unit
  tests + the 3 pre-existing placeholder tests, all passing. NOT yet
  verified end-to-end against a rebuilt `bin/simple` binary (a full seed
  rebuild is out of scope for this lane — see "Verification" below). A
  parallel, currently-*unreachable* copy of the same bug pattern exists in
  the pure-Simple self-hosted compiler's mirror module; see "Pure-Simple
  mirror" below — NOT fixed (deliberately, see reasoning there).
- **Found via:** lane TMF1 (mission-critical robustness campaign), bisecting
  `test/01_unit/compiler/backend/type_mapper_spec.spl`'s "handles composite
  types using each backend strategy" failure (see bonus-find update in
  `doc/08_tracking/bug/wildcard_import_c_backend_stubs_function_to_int_2026-07-30.md`)

## Symptom

```simple
val pairs = [("count", 1), ("ready", 2)]
val out = pairs.map("{_.0}: {_.1}")
```

fails with:

```
semantic: variable `__p1` not found
```

Reproduced standalone in a fresh single-`it`, single-`describe` spec file
with zero other imports/tests (rules out test-state leakage across `it`
blocks or files):

```simple
describe "probe4 isolated":
    it "two bare placeholders different index no call, isolated file":
        val pairs = [("count", 1), ("ready", 2)]
        val out = pairs.map("{_.0}: {_.1}")
        expect(out.join(", ")).to_equal("count: 1, ready: 2")
```

`bin/simple test --no-session-daemon <that file>` → `Results: 1 total, 0
passed, 1 failed`, same `variable __p1 not found` message.

Re-reproduced 2026-07-30 (lane TPL1) with a minimal `run` (not `test`)
probe against the CURRENTLY DEPLOYED `bin/simple`:

```simple
fn main():
    val xs = [1, 2, 3]
    val ys = xs.map("{_} -> {_}")
    for y in ys:
        print(y)
```

```
$ bin/simple run /tmp/.../tpl1_probe.spl
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
[INFO] JIT compilation failed, falling back to interpreter: ...
error: semantic: variable `__p1` not found
```

**Important correction to the original investigation (see "Why the original
static trace hit a contradiction" below): the deployed `bin/simple` in this
environment is currently the Rust seed, not a self-hosted pure-Simple
binary** (its own WARNING banner says so). All of the original lane's
bisection AND its static tracing were performed/reasoned against
`src/compiler`'s pure-Simple `_FlatAstBridge`/`placeholder_lambda.spl` — but
that code never ran for this repro. The real, executing logic lives in
`src/compiler_rust/parser/src/expressions/placeholder.rs`.

## Bisection (all against `bin/release/x86_64-unknown-linux-gnu/simple`, 2026-07-30)

| shape | result |
|---|---|
| `pairs.map("{_.0}")` (single bare placeholder) | PASS |
| `pairs.map("{_.1}")` (single bare placeholder) | PASS |
| `pairs.map(_.0)` (bare shorthand, no template at all) | PASS |
| `pairs.map("{double(_)}")` (single placeholder, wrapped in a call) | PASS |
| `pairs.map("{_.0}: {_.1}")` (TWO bare placeholders, no call) | **FAIL** — `variable __p1 not found` |
| `pairs.map("{_.0}-{_.0}")` (same index used twice) | **FAIL** — `variable __p1 not found` |
| `["a","b"].map("{_}-{_}")` (no `.0`/`.1` at all, just two bare `_`) | **FAIL** — `variable __p1 not found` |
| `pairs.map("{_.0}: {double(_.1)}")` (second placeholder wrapped in a call) | **FAIL**, but with a DIFFERENT message — `cannot convert function to int` (this is the OTHER, separate bug — see below) |

So the minimal failing shape needs no tuple indexing, no nested call, and no
method call at all — just the SAME bare `_` identifier appearing twice inside
one template's `{...}` regions. This is a distinct bug from the one fixed
alongside it in `wildcard_import_c_backend_stubs_function_to_int_2026-07-30.md`
(that one requires a nested call/method-call argument and fails with
"cannot convert function to int" / "cannot access field on value of type
function" — a lambda value reaching a plain-value parameter). **That fix
(commit `28c221afc06`, adding `placeholder_transform_suppressed`) lives
entirely in `src/compiler` (the pure-Simple self-hosted compiler) and, per
the correction above, is not exercised by the currently-deployed seed
binary at all** — the seed has its own, structurally different mechanism
(`call_arg_depth`, see `src/compiler_rust/parser/src/expressions/postfix.rs:17`)
that happens to prevent the analogous nested-call scenario there already
(unverified whether it fully covers the same cases; out of scope for this
lane).

## Root cause (pinned down, 2026-07-30, lane TPL1)

**File/mechanism:** `src/compiler_rust/parser/src/expressions/placeholder.rs`,
functions `count_placeholders` and `replace_placeholders`, in their
`Expr::FString { parts, .. }` match arms (pre-fix: `count_placeholders`
around line 312, `replace_placeholders` around line 420, delegating to the
now-deleted `replace_fstring_parts` around line 629).

**Call chain:**
1. `pairs.map("{_.0}: {_.1}")` is parsed by the seed's *native* f-string
   parser directly into `Expr::FString { parts: [Expr(TupleIndex(Ident("_"), 0)),
   Literal(": "), Expr(TupleIndex(Ident("_"), 1))] }` — the seed parses
   interpolation regions into real sub-expressions at PARSE time (no
   verbatim-text-then-late-reparse step like the pure-Simple compiler's
   FlatAstBridge).
2. `.map` is on the seed's `name_is_higher_order_callback_callee` allowlist
   (`postfix.rs`), so `transform_placeholder_args_for_call` calls
   `force_transform_placeholder_lambda(fstring_expr)` UNCONDITIONALLY on the
   whole f-string argument (`postfix.rs:13`).
3. `force_transform_placeholder_lambda` → no numbered placeholders → falls to
   `count_placeholders(&expr)`. For `Expr::FString`, the **pre-fix** code
   summed `count_placeholders` over every part: `1` (for `_.0`) `+` `1` (for
   `_.1`) `= 2`.
4. `replace_placeholders(expr, &mut counter)` then walks the same parts with
   ONE shared, per-occurrence-incrementing counter: the first `_` (in `_.0`)
   becomes `__p0` (counter 0→1), the second `_` (in `_.1`) becomes `__p1`
   (counter 1→2).
5. `force_transform_placeholder_lambda` then builds
   `params = (0..placeholder_count).map(|i| LambdaParam{name: "__p{i}"})`
   → **two** parameters, `__p0` and `__p1`, producing
   `\__p0, __p1: "{__p0.0}: {__p1.1}"`.
6. But `.map()`'s runtime calling convention supplies exactly **one**
   argument per element. `__p0` gets bound; `__p1` never does. Later, when
   evaluating the body's `{__p1.1}` reference, name resolution fails:
   `semantic: variable \`__p1\` not found`.

**Why this is a bug, not intended behavior:** the file's own header docs
state the intended general-expression semantics — `_ + _` legitimately means
TWO distinct positional lambda parameters (`\__p0, __p1: __p0 + __p1`), which
is correct for ordinary multi-arg callback shorthand (`.reduce(_ + _)`, etc).
But inside ONE string template passed to a single-argument callback like
`.map`, EVERY bare (unnumbered) `_` — no matter how many times it appears
across the template's `{...}` regions — refers to the SAME implicit bound
value (the one argument `.map` supplies per call). The f-string arms of
`count_placeholders`/`replace_placeholders` reused the generic "sum
per-occurrence" strategy verbatim from the general-expression case instead
of collapsing to "at most one shared slot," which is exactly why the
"same index used twice" bisection row (`"{_.0}-{_.0}"`) also fails — that
row is proof this was never about distinct positions, only occurrence
count. The already-correct NUMBERED-placeholder path
(`find_max_numbered`/`replace_numbered_placeholders`) does not have this
bug: it looks up slots BY NUMBER, so `_1` used twice already correctly
collapses to one parameter — the unnumbered path just never mirrored that
design.

## Fix applied (lane TPL1, 2026-07-30)

In `src/compiler_rust/parser/src/expressions/placeholder.rs`:

- `count_placeholders`'s `Expr::FString` arm now returns `1` if ANY part
  contains a bare placeholder (`count_placeholders(part) > 0`), `0`
  otherwise — presence, not a per-occurrence sum.
- `replace_placeholders`'s `Expr::FString` arm now reserves exactly ONE slot
  from the outer counter (only if the f-string has a bare placeholder at
  all) and replaces EVERY bare `_` inside that f-string (across all parts,
  and recursively through any sub-expression shape) with that SAME fixed
  slot, via two new helpers: `replace_fstring_parts_shared_slot` and
  `replace_bare_placeholder_fixed` (a structural mirror of
  `replace_placeholders` that takes a fixed `slot: usize` instead of a
  `&mut usize` counter). The now-unused old per-occurrence
  `replace_fstring_parts` helper was deleted (dead code).
- Added 2 regression tests in the same file's `#[cfg(test)] mod tests`:
  `two_bare_placeholders_in_one_fstring_share_one_param` (the `"{_.0}: {_.1}"`
  shape) and `same_bare_placeholder_reused_twice_in_one_fstring_shares_one_param`
  (the `"{_.0}-{_.0}"` shape). Both assert exactly one lambda parameter
  (`__p0`) and that every occurrence in the rewritten body references it.

**Verification:** `cargo check -p simple-parser --lib --tests` compiles
clean (no warnings). `cargo test -p simple-parser --lib placeholder` — **7
passed, 0 failed**: the 2 new regression tests plus all 5 pre-existing
placeholder tests (numbered-in-fstring, formatted bare-in-fstring,
tuple-index-in-fstring, asm-braced-raw, gherkin-step), so the fix does not
regress the numbered-placeholder path, the format-spec path, or the
tuple-index path.

**Not done:** a full rebuild of the `simple` seed binary (`cargo build -p
simple-driver --bin simple`) and re-run of the exact `bin/simple run`
repro. This lane judged that out of scope given the size/time of a full
seed build in a shared working copy, and unnecessary given the unit-level
verification above directly exercises the exact synthesized-AST shape that
previously produced the wrong parameter count. Whoever next rebuilds/
redeploys the seed should re-run the `xs.map("{_} -> {_}")` probe as a final
end-to-end confirmation.

## Pure-Simple mirror — PORTED 2026-07-30 (lane TPL2)

`src/compiler/10.frontend/desugar/placeholder_lambda.spl`'s
`count_placeholders`/`replace_placeholders` had an `EXPR_INTERPOLATED_STRING`
arm with the **exact same bug pattern** as the Rust seed (sums/replaces
per-occurrence across `parts` with one shared, incrementing `_ph_counter`).
Lane TPL2 ported the same "collapse bare `_` to presence, replace all
occurrences in one template with a shared fixed slot" fix from the Rust seed
(commit `92b91373855`, `src/compiler_rust/parser/src/expressions/placeholder.rs`):

- `count_placeholders`'s `EXPR_INTERPOLATED_STRING` arm now returns presence
  (0 or 1: any part containing a placeholder) instead of a per-occurrence
  sum.
- `replace_placeholders`'s `EXPR_INTERPOLATED_STRING` arm now reserves ONE
  slot from `_ph_counter` when any part has a bare placeholder, and replaces
  every bare `_` across all parts with that same fixed slot via a new
  `replace_placeholders_fixed_slot(eid, slot)` helper (mirrors the Rust
  `replace_bare_placeholder_fixed`/`replace_fstring_parts_shared_slot`
  pair). Numbered placeholders (`_1`, `_2`, ...) and non-f-string shapes are
  unchanged.
- Regression spec added:
  `test/01_unit/compiler/frontend/placeholder_lambda_fstring_shared_slot_spec.spl`
  (two bare `_` share one param; two distinct numbered placeholders `_1`/`_2`
  still get two params).

**Still dead code, unchanged from the original finding:** as the original
lane's dead-end analysis established (and TPL2 re-confirmed by grep against
`origin/main` and the current tree), `expr_interpolated_string()` — the only
constructor for the `EXPR_INTERPOLATED_STRING` tag — is called from nowhere
except `placeholder_lambda.spl` itself (`replace_placeholders` and the new
`replace_placeholders_fixed_slot`); the pure-Simple compiler's actual
string-interpolation path (`_FlatAstBridge/convert_nodes.spl`:
`flat_bridge_build_string_interps`/`flat_bridge_parse_interp_inner`) builds a
structurally different frontend node (`ExprKind.StringLit(str_val, str_interps)`)
and never touches `transform_placeholder_lambda` for the f-string-as-a-whole
at all (the flat parse-time argument is an opaque, un-interpolated string
literal; `parse_call_arg`'s call to `transform_placeholder_lambda` on it is
therefore always a no-op). So TPL2's fix is *correctness parity*, not a live
functional fix: it makes `EXPR_INTERPOLATED_STRING` handling correct for
whenever it becomes reachable, but `xs.map("{_} -> {_}")` compiled through
the current self-hosted pipeline does not exercise this code path either
before or after this change. Whoever wires actual f-string-as-lambda
desugaring into the self-hosted compiler's `EXPR_INTERPOLATED_STRING` path
gets the shared-slot fix "for free" once that wiring lands.

**Verification status:** unverifiable by running the added spec against the
currently-deployed `bin/simple` — edits to `src/compiler/**.spl` do not take
effect without a self-hosting rebuild/redeploy. The spec was run anyway
(`bin/simple test --no-session-daemon
test/01_unit/compiler/frontend/placeholder_lambda_fstring_shared_slot_spec.spl`)
and both examples fail on the deployed binary with `semantic: array index
out of bounds: index is N but length is 0`. A control spec exercising the
pre-existing, UNMODIFIED `_ + _` -> 2-param-lambda path (not touched by this
fix) hit the identical error on the same binary, confirming this is a
pre-existing limitation of exercising `expr_lambda`'s list-array arena
constructor from a spec on the currently-deployed binary, not a regression
introduced by this change. Re-run both specs after the next self-hosted
redeploy.

## Dead ends from the original investigation (SUPERSEDED by the root cause above,
## preserved verbatim from the initial filing so nobody retraces them)


`__p0`/`__p1`-style names are generated in exactly one place in the whole
compiler: `src/compiler/10.frontend/desugar/placeholder_lambda.spl`
(`transform_placeholder_lambda`/`replace_placeholders`, string patterns
`"__p{i}"` and `"__p{_ph_counter}"` and `"__p{param_idx}"`). Verified via
repo-wide grep (`grep -rn '__p[0-9]\|"__p"' src/compiler`) that no other file
anywhere generates this naming pattern, by any concatenation form. So the
`__p1` reference MUST originate from that module's logic somehow being
invoked on this template.

`transform_placeholder_lambda` is itself only ever CALLED from 3 sites (grep
`transform_placeholder_lambda(` repo-wide): two pipe-operator (`|>`) call
sites in `parser_expr.spl`, and `parse_call_arg()`
(`src/compiler/10.frontend/core/parser_expr.spl:657`), which runs on every
call/method-call argument in the language.

But the two bare regions `_.0` and `_.1` in `"{_.0}: {_.1}"` are NOT call
arguments — they are parsed via a completely separate path:
`_FlatAstBridge/convert_nodes.spl:flat_bridge_build_string_interps` splits the
literal on top-level `{...}` regions and, for each one, calls
`flat_bridge_parse_interp_inner(inner)`, which does a **fresh**
`lex_init_with_path(inner.trim(), "")` + `parser_advance()` + `parse_expr()`
— NOT `parse_call_arg()`. `parse_expr()` → `parse_pipe()` → ... → `parse_primary()`
for a bare `_.0` (identifier + field access, no parens) never reaches
`parse_call_arg` at all when there is no nested call in the region. Static
tracing therefore predicts these two regions should come out as plain,
unrenamed `Ident("_")` nodes (this DOES appear to be what happens for the
single-placeholder-per-template cases, which all pass). Yet the double-bare
case reproducibly fails referencing `__p1` — a contradiction with the static
trace that was not resolved in this lane.

Also checked and ruled out:
- `expr_interpolated_string()` (the constructor for the flat-arena
  `EXPR_INTERPOLATED_STRING` tag, which `placeholder_lambda.spl`'s own
  `EXPR_INTERPOLATED_STRING` case in `count_placeholders`/`replace_placeholders`
  DOES recurse over multiple `parts` with a shared counter — which WOULD
  reproduce exactly this bug if reachable) is constructed in exactly one place
  repo-wide: inside `replace_placeholders` itself. No other code builds this
  node, so (as far as static grep can show) that code path is never actually
  fed a fresh `EXPR_INTERPOLATED_STRING` from outside — but this is the
  single most likely site if some other construction path was missed.
- HIR lowering (`20.hir/hir_lowering/expressions.spl`, `lower_interpolation_list`)
  and MIR lowering (`50.mir/_MirLoweringExpr/expr_dispatch.spl`,
  `split_interpolation_segments`/`lower_string_interpolation`) both only
  consume an already-built `interps`/`HirInterpolation` list generically; no
  `_`/placeholder-aware logic found there.
- Ruled out cross-test/file state leakage from `_ph_counter` (a module-level
  var in `placeholder_lambda.spl`) by reproducing in total isolation (single
  `it`, single `describe`, single file, zero other imports).

## Suggested next step

Since a rebuild of the self-hosted binary is required to test any fix (see
the sibling doc's "Not yet verified" note — same constraint applies here),
the fastest way to actually resolve this without more blind static tracing is
to add a temporary `eprint` at the top of `transform_placeholder_lambda` (and
at `expr_interpolated_string`'s one call site) showing `eid`/`tag`, rebuild
once, and run the isolated repro above to get a real call trace instead of
guessing further from source reading alone.


## Why the original static trace hit a contradiction (historical note, corrected)

The original investigation (this section preserved from the initial filing)
reasoned entirely from `src/compiler`'s pure-Simple frontend and predicted
that a bare `_.0`/`_.1` region should come out unrenamed — a prediction that
in fact holds **for the pure-Simple compiler's own `EXPR_STRING_LIT`
conversion path**, which is why it contradicted the observed failure: the
investigation was tracing the wrong binary. The bisection table above was
run against `bin/release/x86_64-unknown-linux-gnu/simple`, which prints its
own "this Rust-built Simple binary is a bootstrap seed only" warning on
every invocation — i.e. it is (and, per this lane's re-check, still is) the
Rust seed, not a rebuilt self-hosted binary. Lesson for future lanes: when a
bisection's own static trace contradicts its own reproduction, check which
binary is actually deployed at `bin/simple` before concluding the trace (or
the repro) is wrong.

## Workaround

None found that keeps the placeholder form. Rewrite as an explicit lambda:
`pairs.map(\p: "{p.0}: {p.1}")` instead of `pairs.map("{_.0}: {_.1}")`.
