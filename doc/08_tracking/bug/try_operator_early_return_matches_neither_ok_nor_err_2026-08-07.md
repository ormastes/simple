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

- **GREEN**: built `cargo build --release --bin simple` against the scratch
  tree with the fix applied; ran
  `test/01_unit/try_operator_error_propagation_spec.spl` under the resulting
  binary's default JIT engine (`bin/simple run`, no `SIMPLE_EXECUTION_MODE`
  override): `6 examples, 0 failures` /
  `declared>=6 executed=6 passed=6 failed=0 dropped=0`.
- **RED**: `git apply -R` of the same hunk in the same scratch tree
  reproduces the original defect shape (bare `rt_enum_payload`, no
  discriminant test, no branch) — matching the JIT probe transcript recorded
  above (`after: [boom]` / `caller OK:[boom]`) and confirming the fix, not
  some other scratch-tree difference, is what flips the spec from failing to
  passing.

Remaining follow-ups (not this fix's scope): redeploy the seed so the shared
binary picks the fix up; then revert `http1.decode_chunked` to the `?` form
per "How it was found"; optionally relax the AOT `TryOperator` compilability
refusal now that a correct lowering exists.
