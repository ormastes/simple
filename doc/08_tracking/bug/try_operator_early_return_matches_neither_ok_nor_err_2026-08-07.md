# `?` early-return produces a value that matches neither Ok nor Err (seed)

- **Status:** FIXED AT SOURCE (2026-08-07) — seed `lower_try` now emits the
  discriminant-test + early-return shape (see "Fix (landed)" at the bottom).
  The deployed shared `bin/release/<triple>/simple` still carries the OLD
  behavior until the next seed rebuild/redeploy; that redeploy is deliberately
  NOT done here (shared binary, in concurrent use by other sessions).
- **Root cause found:** 2026-08-07 (see "Root cause" below)
- **Found:** 2026-08-07
- **Area:** `?` (try) operator — seed runtime, observed via `bin/simple run`
- **Severity:** high — an error propagated with `?` is silently LOST at the call
  site; the caller's `match` falls through every arm and execution continues

## Symptom

When a function propagates a failure with `?`, the `Result` the caller receives
matches **neither** `case Ok(...)` nor `case Err(...)`. No arm runs, nothing is
printed, and no error is raised — the call simply evaporates.

Minimal repro (seed interpreter, rc=0):

```simple
fn inner_tuple(bad: bool) -> Result<tuple, text>:
    if bad:
        return Err("boom")
    Ok(("payload", 1))

fn outer_try(bad: bool) -> Result<text, text>:
    val p = inner_tuple(bad)?
    return Ok(p.0)

fn outer_match(bad: bool) -> Result<text, text>:
    match inner_tuple(bad):
        case Ok(p): return Ok(p.0)
        case Err(e): return Err(e)

fn show(label: text, r: Result<text, text>):
    match r:
        case Ok(v): print(label + " OK:[" + v + "]")
        case Err(e): print(label + " ERR:[" + e + "]")

fn main():
    show("try   good:", outer_try(false))
    show("try   bad :", outer_try(true))
    show("match good:", outer_match(false))
    show("match bad :", outer_match(true))
```

Actual output — the `try bad` line is **absent entirely**:

```
try   good: OK:[payload]
match good: OK:[payload]
match bad : ERR:[boom]
```

Expected: `try bad : ERR:[boom]`, identical to `match bad`.

The success path through `?` is fine; only the error path is broken. The
hand-written `match` is correct in both directions, which isolates the fault to
`?` rather than to `match`, to `Result`, or to the tuple payload.

## Why this matters

`.claude/rules/language.md` makes `Result<T, E>` + `?` **the** sanctioned error
mechanism ("no try/catch/throw keywords — by design"). A `?` that drops errors
means every function using the sanctioned idiom can silently swallow failures.
It is also a fail-open verification trap: a probe that only exercises the happy
path sees `?` working perfectly.

## How it was found

While repairing `decode_chunked` (see
`decode_chunked_malformed_size_silently_truncates_body_2026-08-06.md`),
`http1.decode_chunked` was first written as:

```simple
val pair = decode_chunked_with_trailers(encoded)?
return Ok(pair.0)
```

Its two error probes printed blank lines while the success probes were correct.
Rewriting the body as an explicit `match` made all cases pass. That workaround
is in the shipped code and is marked here rather than being normalised silently.

## Fix direction

Start by inspecting the desugaring of `?` in the seed and comparing the value it
early-returns against the one the explicit `match` arm constructs.

**No root cause is claimed here.** What was observed is the symptom and its
isolation: the success path through `?` is correct, the hand-written `match` is
correct in both directions, and only the `?` error path is lost. The
desugaring was not read, so any statement about *why* would be speculation —
deliberately left out so the next lane is not pointed down an unverified path.

Once fixed, revert `http1.decode_chunked` to the `?` form and re-run the probe
above; it must print `try bad : ERR:[boom]`.

---

# Root cause (2026-08-07)

## It is worse than "matches neither arm": `?` emits NO BRANCH AT ALL

The original report inferred an early return whose value was mis-tagged. There
is no early return. Probe (`print` on both sides of the `?`):

```simple
fn outer(bad: bool) -> Result<text, text>:
    print("  before")
    val p = inner(bad)?
    print("  after: [" + p + "]")
    return Ok(p)
```

JIT output for `bad=true`:

```
  before
  after: [boom]        <-- execution CONTINUED past the `?`
caller OK:[boom]       <-- the ERROR PAYLOAD came back as the Ok payload
```

`?` unwraps the payload **unconditionally**. On `Err` it binds the *error*
payload to the value binding and falls through. The caller's `match` does select
the `Ok` arm — the original "neither arm" reading was an artifact of the
tuple-typed repro reinterpreting a `text` payload.

Corroborating matrix (JIT, `bad=true` for each):

| operand type | expected | observed |
|---|---|---|
| `Result<text, text>` | `ERR:boom` | `OK:[boom]` — error payload returned as success |
| `Result<i64, text>`  | `ERR:boom` | `OK:[n=5867001622113]` — payload pointer read as `i64` |
| `Result<tuple, text>`| `ERR:boom` | blank — `text` payload indexed as a tuple |
| bare `f()?` stmt, no binding | `ERR:boom` | `OK:[done]` — fell straight through |

The fault is **not** payload-type dependent, **not** binding-form dependent, and
**not** cross-module dependent.

## The exact defect (Rust seed)

`src/compiler_rust/compiler/src/hir/lower/expr/control.rs:2194`, `lower_try`:

```rust
pub(super) fn lower_try(&mut self, inner: &Expr, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
    let inner_hir = self.lower_expr(inner, ctx)?;
    let payload_ty = self.result_like_payload_type(inner_hir.ty).unwrap_or(TypeId::ANY);
    Ok(HirExpr {
        kind: HirExprKind::BuiltinCall {
            name: "rt_enum_payload".to_string(),
            args: vec![inner_hir],
        },
        ty: payload_ty,
    })
}
```

`expr?` becomes a bare `rt_enum_payload(expr)` — no `rt_enum_discriminant` test,
no branch, no return. That is precisely the observed behaviour.

## The correct implementation exists in the seed and is UNREACHABLE

`MirInst::TryUnwrap` is fully implemented on every backend:

- `src/compiler_rust/compiler/src/codegen/instr/result.rs` — `compile_try_unwrap`
  does the right thing: `rt_enum_discriminant(v) == variant_disc("Err")` →
  `brif` to the caller-supplied `error_block`, else `rt_enum_payload(v)`.
- `codegen/instr/mod.rs:1058` (cranelift), `codegen/llvm/functions.rs:1777`
  (LLVM), `codegen/dispatch.rs:294`, `mir/inst_enum.rs:643`.
- Unit tests in `codegen/codegen_instr_tests.rs:675`,
  `codegen/codegen_shared_tests/memory_tests.rs:482`.

**Nothing in MIR lowering ever emits `MirInst::TryUnwrap`.** A grep for
`TryUnwrap` across `src/compiler_rust/compiler/src/` returns only the
implementations above and their unit-test constructions. The whole `?`
early-return machinery is dead code that `lower_try` routes around. The unit
tests are green because they hand-build the MIR instruction themselves — a
textbook fail-open: the instruction is proven correct and proven never used.

## The pure-Simple compiler is CORRECT

`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:2501`,
`lower_try_expr`, emits `try_err` / `try_ok` blocks and calls
`terminate_return(res_local)` on the Err path — the sanctioned semantics. The
headline is therefore inverted from the usual: **the pure-Simple lowering is
right; the seed that everyone actually runs is wrong.** No pure-Simple fix is
required. (This could not be executed to confirm — Stage 3 is blocked, so there
is no deployed pure-Simple binary. The claim is a source reading, not a run.)

## Per-engine behaviour

| engine | selector | verdict |
|---|---|---|
| interpreter | `SIMPLE_EXECUTION_MODE=interpret` | **CORRECT.** `interpreter/expr.rs:390` raises `CompileError::TryError` and propagates. Probe prints `caller ERR:[boom]`. |
| JIT (default for `bin/simple run`) | anything not `interpret` | **SILENTLY WRONG**, as above. |
| native AOT | `bin/simple compile --native` | **REFUSED** (fail-closed): `error: ... 2 function(s) contain constructs that require the interpreter: - outer: [TryOperator]`. `compilability.rs:620` / `src/compiler/80.driver/compilability.spl:32`. `?` has never been AOT-compilable. |

Note: an earlier `native-build` attempt failed with an unrelated worker error;
the `compile --native` refusal above is the real native verdict.

## Blast radius

Approximately **4,548 postfix-`)?` sites across 526 `.spl` files** in `src/`
(excluding `vendor/`; a separate 103 `.?` sites are a different operator). Every
one of them has a broken error path under the JIT. Concentrations:
`src/lib/nogc_sync_mut` (146 files), `src/lib/nogc_async_mut` (85),
`src/compiler_rust/lib` (72 — the seed's own bundled Simple library is exposed
to the seed's own bug), `src/lib/gc_async_mut` (39),
`src/compiler/70.backend` (28), `src/app/interpreter` (28).

## Regression spec

`test/01_unit/try_operator_error_propagation_spec.spl` — 6 examples covering the
binding form, the bare-statement form, and a non-`text` payload, in both
directions.

```
SPEC FILE VERDICT: ... try_operator_error_propagation_spec.spl declared>=6 executed=6 passed=6 failed=0 dropped=0
```

Proven non-vacuous by sabotage (replacing the `?` in `_try_bind` with a `match`
that binds the error payload as if it were the Ok payload — i.e. reproducing the
defect by hand): `declared>=6 executed=6 passed=5 failed=1 dropped=0`, exactly
the one intended example.

**It is green for the wrong reason and does not guard this bug.**
`bin/simple test` hard-defaults to the tree-walk interpreter
(`.claude/rules/testing.md`: "`run` and `test` are DIFFERENT ENGINES"), and the
interpreter is the one engine where `?` is correct. The spec guards the
semantics and would catch an interpreter or pure-Simple regression; catching the
*JIT* defect needs a probe that runs under `bin/simple run`.

## Fix direction (not landed)

Make `lower_try` reach the already-correct `MirInst::TryUnwrap`, or reproduce
its shape in HIR. Every piece needed is present in the seed:
`HirExprKind::Block(Vec<HirStmt>)`, `HirStmt::Let { local_index, ty, value }`,
`HirStmt::If { condition, then_block, else_block }`, `HirStmt::Return(Option<..>)`,
and `HirExprKind::Local(usize)` — and `control.rs:1668` already uses
`HirExprKind::Block(vec![HirStmt::Return(value)])` in expression position as
precedent. Shape:

```
Block([
  Let  { tmp = <inner> },
  If   { rt_enum_discriminant(tmp) == variant_disc("Err") => [Return(Some(tmp))] },
  Expr ( rt_enum_payload(tmp) ),
])
```

Use the hashed `variant_disc` convention from `codegen/instr/result.rs` (the
same hash `create_enum_value` uses at construction) — **not** `rt_is_ok`-style
helpers, and not a positional index.

Not landed here because it is Rust seed surgery requiring a full rebuild, and
the shared `bin/release/x86_64-unknown-linux-gnu/simple` is in use by ~10
parallel sessions and must not be overwritten to prove a fix.

Once the seed is fixed, revert `http1.decode_chunked` to the `?` form and re-run
the probe; it must print `try bad : ERR:[boom]`.

## Additional verification (2026-08-07, follow-up lane)

Two source claims above were re-checked directly (not relayed secondhand):

- `src/compiler_rust/compiler/src/hir/lower/expr/control.rs:2194` `lower_try` —
  confirmed: body is exactly `rt_enum_payload(inner_hir)`, no discriminant test,
  no branch, no early return.
- `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:2501`
  `lower_try_expr` — confirmed: creates `try_err`/`try_ok` blocks (line
  2700-2701) and calls `terminate_return(res_local)` on the Err path (line
  2713). The pure-Simple-lowering-is-correct claim holds.

The doc previously had no probe run under the JIT to demonstrate the defect
directly (the 6/6 green spec only exercises the interpreter, which `bin/simple
test` defaults to and where `?` is already correct). Ran the doc's own
text-payload repro under both engines directly, no rebuild:

JIT (`bin/simple run`, default engine):
```
  before
  after: [boom]
caller OK:[boom]
```

Interpreter (`SIMPLE_EXECUTION_MODE=interpret bin/simple run`):
```
  before
caller ERR:[boom]
```

This is the missing empirical red: JIT falls through past `?` and returns the
error payload as an Ok value; interpreter correctly short-circuits with no
"after" line at all. No code was changed by this follow-up lane — `lower_try`
is Rust-seed-only and a rebuild was out of scope at the time (shared binary,
per the note above). This empirical red is superseded by "Fix (landed
2026-08-07)" below, which fixes `lower_try` at the source and verifies
RED-then-GREEN in a scratch worktree build; see the Status line at the top of
this doc for the current state.

---

# Fix (landed 2026-08-07)

`lower_try` in `src/compiler_rust/compiler/src/hir/lower/expr/control.rs` now
emits exactly the shape from "Fix direction" above, using the file's existing
HIR devices (`LetIn` temp as in `lower_exists_check`, hashed-variant
`rt_enum_check_discriminant` as in match lowering, one-statement
`Block([HirStmt::Return])` as in the S70 match-arm-return fix):

```text
LetIn tmp = <inner> in
  if rt_enum_check_discriminant(tmp, disc("Err")): return tmp
  else: rt_enum_payload(tmp)
```

Verified in a pristine scratch worktree (`git archive origin/main` at
`6d510cc83e0a2d73b79b7576aa39d0d265ce4da9` + this one hunk applied with `git
apply`). origin/main at that SHA does not build as-is: `mod.rs` already wires
`insert_simple!("rt_dict_free_deep", sffi_array::rt_dict_free_deep_fn)` and the
`rt_free_deep` counterpart, but neither function exists anywhere in
`sffi_array.rs` on that SHA (E0425, unrelated to this fix — belongs to
whichever lane added the `mod.rs` wiring). Unblocked the scratch build only
with two local no-op stubs (`Ok(Value::Int(0))`, no dependency on missing
runtime symbols); **not landed**, not part of this commit's tree.

- **GREEN, minimal probe** (the exact repro from "Root cause" above, run
  directly, not through the spec DSL): `bin/simple run` on the fixed scratch
  binary prints `bad  ERR:[boom]` with no "after" line — matches the
  interpreter and the hand-written `match`, both engine-default and with
  `SIMPLE_EXECUTION_MODE=interpret`/`jit` forced explicitly.
- **RED, minimal probe**: `git apply -R` of the fix hunk in the same scratch
  tree, rebuilt, reproduces the original defect shape exactly (bare
  `rt_enum_payload`, no discriminant test, no branch) — `before` / `after:
  [boom]` / `bad  OK:[boom]`, byte-identical to the transcript recorded in
  "Root cause" above.
- **The landed regression spec does NOT discriminate this defect.**
  `test/01_unit/try_operator_error_propagation_spec.spl` run via `bin/simple
  run <spec>` reports `6 examples, 0 failures` /
  `executed=6 passed=6 failed=0 dropped=0` on **both** the RED and the GREEN
  scratch binary, and under every `SIMPLE_EXECUTION_MODE` value tried
  (unset/default, `interpret`, `jit`). The spec's own comments claim
  "under the defect `try_err_text` returns `Ok(\"boom\")`", but that is not
  what was observed here — the spec passes regardless of whether `lower_try`
  is fixed. This is recorded here rather than silently assumed working: the
  spec's non-vacuity claim is FALSE as currently written, most likely because
  the `describe`/`it`/`expect` spec DSL executes example bodies through a
  path that never goes through the buggy JIT `lower_try` lowering at all
  (consistent with the standing note that the spec DSL runs largely on Rust
  intrinsics rather than compiling and JIT-running the `.spl` source the way
  `bin/simple run` on a plain script does). Root-causing *why* the spec is
  insulated from the engine choice is out of scope for this fix; what is
  confirmed is that the minimal, non-DSL probe above is the only thing in
  this doc that actually discriminates RED from GREEN, and any future claim
  that this spec file is a regression guard for the JIT path should be
  treated as unverified until that gap is closed.

Remaining follow-ups (not this fix's scope): redeploy the seed so the shared
binary picks the fix up; then revert `http1.decode_chunked` to the `?` form
per "How it was found"; optionally relax the AOT `TryOperator` compilability
refusal now that a correct lowering exists.

# Blast-radius audit — bounded (2026-08-08)

The `## Blast radius` section above was an unbounded estimate and was flagged as
an open gap. This section closes it. Pinned to `origin/main` throughout
(`git grep origin/main` — no working-copy contamination).

## Matching rule and its error profile

`?` is an operator only; it never appears in identifiers. Scan of every `.spl`
under `src/`, `test/`, `examples/` (vendored paths excluded), per line:
strip `#` comments and string literals, mask multi-line `"""` regions, then
take `?` tokens preceded by `[A-Za-z0-9_)\]]`, and drop `??`, `.?`, `?.` and
type-position `?` (a `?` followed by `)`, `,`, `]`, `:`, `=`, `->`, `{` or
end-of-line).

Raw token census (51,092 `?` characters in 43,211 candidate lines):

| shape | count | disposition |
|---|---|---|
| `??` | 23,881 | nil-coalescing operator — **not** try |
| `.?` | 13,258 | presence/exists test — Option lane, **unchanged by construction** (the fix tests the hashed `"Err"` discriminant, which `Some`/`None` never match) |
| type-position `?` | ~5,900 | `-> text?`, `field: T?` — nullable **type** syntax, not the operator |
| `?.` + stray | 210 | optional-chaining / prose |
| **try operator** | **7,787** | the audited surface |

Measured precision, hand-checked on 25 random rows drawn from each arm of the
**final** classifier's own output (an earlier draft of this scanner tested
type-position against the raw line rather than the comment/literal-stripped one
and scored far worse; those numbers do not apply here): `)?` call-position
**25/25**, bare-identifier `?` **25/25**. Residual false positives do exist but
are rare enough to miss a 25-sample — both known survivors are type annotations
in call-paren position that the `->`-guard does not cover
(`block_comment: (text, text)? = nil` in `15.blocks/blocks/highlighting.spl:101`,
`resolution_cache: {text: text?}` in `99.loader/module_resolver/types.spl:324`),
so the 119-site bucket 2 below carries a handful of them. False negatives are
concentrated in `?` written inside embedded Simple source in spec fixtures,
which is data, not a call site. Scope: `.spl` only — a `?` in
`src/compiler_rust/**/*.rs` is Rust's own operator.

## The result that bounds everything: the fix was seed-only

**Verified, not taken from the commit message.**
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:2553`
(`lower_try_expr`) already emitted, on the Result path,
`rt_enum_discriminant` -> compare against `err_key = 1` ->
`terminate_return(res_local)` — a real discriminant test and a real early
return — and does the same for both physical Option representations.

So the pure-Simple compiler was **always** correct. Only the Rust seed
swallowed `Err`. The behavior change is therefore confined to code executed by
seed-compiled artifacts (bootstrap stage 1, `bin/simple test`/`run`), and it
moves the seed *toward* what the rest of the toolchain already did. Anything
built by the deployed self-hosted binary has **no** behavior change to audit.

## Risk-ranked classification of all 7,787 try sites

Bucketed by the enclosing function's declared return type (multi-line
signatures accumulated until parens balance — an earlier naive version
mis-reported 392 `src` sites as having no return type; the real figure is 135).

| rank | bucket | sites | verdict |
|---|---|---|---|
| — | `src/` -> `Result<…>` (incl. aliases e.g. `BrowserResult<T>`) | 3,881 | **safe** — propagation is the declared contract; callers already had to handle `Err`. The fix makes the seed match the contract. |
| — | `test/` + `examples/` -> `Result<…>` | 292 | **safe**, same reason |
| **1** | `src/compiler/` -> non-Result **and** body returns `Ok`/`Err` | **16** | **behavior-changed** — see below; **filed, not fixed** |
| 2 | other `src/` non-Result enclosing fn | 119 | known separate hole (raw `Err`-tagged handle as an integer, no diagnostic); pre-existing, not a regression |
| 3a | `test/`/`examples/` non-Result enclosing fn, Option-shaped | ~2,868 | `check(opt? == 42)` / `verify(result? == 99)` — **Option lane, out of scope** |
| 3b | `test/` spec closures at top level of a `describe`/`it` block | 540 | **Result**, not Option — `db.exec("CREATE TABLE …", [])?` in the sql specs. Same known hole as bucket 2 (no enclosing declared return type), same verdict: pre-existing, not a regression |
| — | `src/` Option-typed enclosing fn | 62 | Option lane — noted, not fixed |
| — | `test/` Option-typed enclosing fn | 9 | Option lane — noted, not fixed |

**Zero sites were fixed, and that is the finding**: no site "breaks" in the
sense of a caller that now receives an `Err` it cannot handle. Bucket 1 is the
only genuinely behavior-changed set, and the task's own scope rule ("a `?` in a
function whose return type isn't Result/Option is a known separate hole …
report any you find but don't try to fix that hole here") puts it out of bounds.

## Bucket 1 in full — 16 sites, all in `src/compiler/`, 3 files

Every one is the *same* defect: the function's declared return type says `text`
while its body speaks `Result` (`return Ok(…)` / `return Err(…)`) and its
callers `match … case Ok(…) / case Err(e)`. The declared type is simply wrong.

| file | lines | enclosing fn (declared) |
|---|---|---|
| `src/compiler/00.common/predicate_parser.spl` | 121, 132, 139, 147, 154, 165, 176, 183 | `parse_predicate`, `parse_or`, `parse_and`, `parse_not`, `parse_primary` — all `-> text`; `tokenize` and `make_selector` are `-> text` too |
| `src/compiler/70.backend/backend/common/expression_evaluator.spl` | 99, 108, 119, 120, 132, 133, 176 | `eval_array_lit`, `eval_tuple_lit`, `eval_dict_lit`, `eval_binary_op`, `eval_unary_op` — all `-> text`, all bodies `Ok(…)` |
| `src/compiler/70.backend/arch_rules.spl` | 181 | `parse_arch_rules_block -> text`, calls `parse_predicate(…)?` |

Post-fix these now genuinely early-return an `Err`-tagged handle out of a
function declared `-> text`.

**Why filed and not fixed.** The intent looks obvious (`parse_or` should be
`Result<(Predicate, i64), text>`) but it is not safely actionable here:

1. These files are **known refactor damage with an OPEN family** owned by
   another lane — the two most recent commits touching them are
   `b0c98541d2a` ("restore folded-receiver method calls (shape (d) refactor
   damage)") and `9d4d16b106e` ("restore 22 zero-definition call sites; family
   still OPEN (29 remain)"). Rewriting return types underneath that lane risks
   a clobber.
2. `expression_evaluator.spl` has a sibling `expression_evaluator_bootstrap.spl`
   selected by `backend/common/mod.spl`, so the bootstrap-active variant may not
   even be the damaged one — which of the two is authoritative is undecided.
3. The mismatch is **not local to these 3 files**: a mechanical scan of all
   35,719 owned `.spl` files finds **1,385 functions** (888 in `src/`) declared
   with a non-`Result` return type whose body still returns `Ok(…)`/`Err(…)`.
   Fixing 3 files would be arbitrary. This class needs its own lane.

## Secondary finding: the two compilers disagree on the Err discriminant

The seed's fixed `lower_try` tests a **hashed** variant-name discriminant
(`rt_enum_check_discriminant(tmp, hash("Err"))`, the seed's stated convention,
shared with its match lowering). The pure-Simple `lower_try_expr` tests
**positional index 1**. Each is self-consistent because each also *constructs*
its enums with its own convention, so this is not a live defect today. It
becomes one the moment an enum value constructed by seed-compiled code is
`?`-tested by pure-Simple-compiled code in the same process. Recorded here so
the convention split is not rediscovered as a mystery later.

## Checked and cleared: the fix does not skip resource cleanup

The pure-Simple `lower_try_expr` calls `emit_pending_resource_drops(nil)`
immediately before its `terminate_return` on the Err path. The seed's new
`lower_try` emits a bare `HirStmt::Return` with no such step, which would be a
*new* leak on the Err path — an early return skipping cleanup that previously
always ran — if the seed had cleanup to skip. It does not: `git grep` for
`emit_pending_resource_drops`, `pending_resource_drops`, `ResourceDrop`,
`resource_drop` and `scope_exit_drops` across `src/compiler_rust/compiler/src/**`
returns **zero** hits. The Rust seed has no resource-ownership machinery at all,
so there is no drop for the new early return to bypass.

## Honest summary

The surface is large — 7,787 try sites — but almost all of it is safe, for a
reason that is verified rather than assumed: the pure-Simple lowering was
already correct, so the fix only converges the seed onto behavior the rest of
the toolchain already had, and 4,173 of the 7,787 sites sit in functions that
already declare `Result` and whose callers already handle `Err`. The residue is
16 compiler sites in a documented, pre-existing, out-of-scope defect class.
