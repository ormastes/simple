# ANY-typed slots hold RAW untagged scalars (JIT) — 2026-08-05

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
(commit `688e40ff147243f2de8118ef071ccf96ce8e17ca`, confirmed on
`origin/main`) — see "Pure-Simple parity gap — storage side FIXED" below.
**Consumer-side gap (`.to_text()` / `==`) still OPEN** — see "Pure-Simple
parity gap — consumer side, STILL OPEN, 2026-08-06" below.

## Symptom

Under the Cranelift JIT, a scalar stored into an `Any`-typed slot was stored
RAW (untagged). Every consumer that assumes a tagged `RuntimeValue` then
misread the low 3 bits as tag bits:

```
val ab: Any = true    ab.to_text()  ->  "nil"           (raw 1  -> SPECIAL_NIL)
val ai: Any = 42      ai.to_text()  ->  denormal float  (raw 42 -> TAG_FLOAT)
val af: Any = 10.0    af.to_text()  ->  "0"
val at: Any = "hi"    at.to_text()  ->  "hi"            (heap ptr already tagged — fine)
```

This is the `<value:0x6>` / denormal-float artifact family. `<value:0x{:x}>` at
`src/compiler_rust/runtime/src/value/sffi/io_print.rs:464` is the faithful
REPORTER of an untagged value, not the bug.

**Not only cosmetic.** Measured by value, not by rendering:

```
OLD JIT:  ai == 42    -> false        af == 10.0 -> false
NEW JIT:  ai == 42    -> true         af == 10.0 -> true
```

An earlier reading that "the value is intact, only `to_text` is wrong" holds
for *pattern bindings* (a different path) but NOT for a local `Any` declaration,
where the comparison is wrong too.

## Engine divergence — why the suite was blind

| | local `Any` bool / i64 / f64 |
|---|---|
| JIT (`simple run`) | BROKEN (before this fix) |
| interpreter (`simple test`) | correct, always |

The spec suite hard-defaults to the interpreter, so no spec could observe this.
Reproduce only via `bin/simple run`, never via `bin/simple test`.

## Root cause

There is no single widen/box site. Boxing is per-consumer, and two consumers
were missing it:

1. `mir/lower/lowering_expr_call.rs` `box_arg_for_any_param` — matched
   `I8..U64` -> `BoxInt` and `F32/F64` -> `BoxFloat`, but `TypeId::BOOL`
   appeared nowhere, so a bool argument reached an `Any` parameter raw.
   (The sibling `box_enum_payload_if_needed` in the same file DOES list BOOL.)
2. `mir/lower/lowering_stmt.rs` `HirStmt::Let` — stored the initializer with no
   box at all, for every scalar type.

The correct block already existed ~700 lines away in the same file, in the
`HirExprKind::Global` assign arm: it gates on `target_is_any` and does all
three (`rt_value_bool` / `BoxInt` / `BoxFloat`). `HirStmt::Let` was simply
missing it. Both fixes copy that proven block.

**Bool must use `rt_value_bool`, never `BoxInt`.** Bool is `TAG_SPECIAL`
(`0b011`) with `SPECIAL_TRUE=1`/`SPECIAL_FALSE=2` (`runtime/src/value/tags.rs`),
i.e. raw 11/19. `BoxInt` yields a tagged INT 1 and renders `"1"` instead of
`"true"` — verified by deliberate sabotage, see the fix commit. There is no
`MirInst::BoxBool`; that asymmetry is what left this gap open, and adding one
would remove the whole class.

## Pure-Simple parity gap — storage side FIXED (2026-08-06)

`src/compiler/` had the same gap. **Both storage-side sites are now fixed**,
each with a small `case HirTypeKind.Any:` arm calling the existing
`box_runtime_value` (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`,
proven correct including the bool `TAG_SPECIAL` encoding — verified by hand:
`true` -> raw 11, `false` -> raw 19, matching `SPECIAL_TRUE=1`/`SPECIAL_FALSE=2`
above):

- Local `Let` (the LIVE `disc==1` early-Let path, not the dead second
  `case Let(...)` arm ~250 lines further down — that second arm is
  unconditionally unreachable for a Let statement, see the `return` at the end
  of the disc==1 block): `src/compiler/50.mir/mir_lowering_stmts.spl:516`
  (`match declared_type.kind:` inside the `Some(declared_type)` arm), new
  `case HirTypeKind.Any: init_local = self.box_runtime_value(init_local)`.
- Call args: `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:4131`
  (`match declared_param_type.kind:`), new
  `case HirTypeKind.Any: arg_local = self.box_runtime_value(arg_local)`.

Commit `688e40ff147243f2de8118ef071ccf96ce8e17ca`
("fix(mir): box scalar values assigned into Any-typed locals/params"),
confirmed present on `origin/main` via `git fetch origin main && git
merge-base --is-ancestor <sha> origin/main`. Landed via this session's
automatic working-copy sync (the diff matches the intended edit exactly, 2
files / 29 insertions, nothing else swept in) rather than an explicit `jj
commit` — confirm provenance the same way (`git show --stat <sha>`) if this
looks surprising later.

**Verification caveat:** a fresh self-hosted-compiler rebuild (needed to
exercise the NATIVE/JIT path this bug lives on — the interpreter is already
correct and cannot observe it, see "Engine divergence" above) could not be
completed in-session. Two `SIMPLE_NATIVE_INCREMENTAL=1` attempts against
`build/native_cache` (entry `src/app/cli/bootstrap_main.spl`, sourcing
`src/compiler` + `src/lib` + `src/app/cli`) each ran 40-55 minutes of real CPU
time under extreme concurrent host load (`load average` 10-20, swap
frequently full) without producing a binary, and the tracked background task
was terminated before completion. A `bin/simple lint` pass on both edited
files came back **0 errors** (109 pre-existing unrelated warnings), which
confirms the new arms are syntactically/structurally valid, but this is NOT a
substitute for the runtime `.to_text()`/`==`/call-arg repro the fix shape
calls for. Re-run under lighter host load:
```
val ab: Any = true;  val ai: Any = 42;  val af: Any = 10.0
# via `bin/simple run`, NOT `bin/simple test`
```
and compare against the OLD/NEW symptom tables above.

## Pure-Simple parity gap — consumer side, STILL OPEN (2026-08-06)

The storage-side fix above is necessary but **not sufficient** for
`.to_text()`/`==` to read correctly on a pure-Simple `Any` local, because two
consumer-side sites are type-directed in the Rust seed but are NOT ported to
pure-Simple's dynamic (`is_runtime_value_local`) tracking model. Found by
reading the Rust seed's already-fixed comparison lowering
(`src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs:116-150`) for
the mechanism behind the doc's own "NEW JIT: `ai == 42` -> true" claim, then
checking pure-Simple's equivalent sites — **do not treat this section as
verified by a passing run; it is a static-trace finding pending the rebuild
above.**

1. **Comparison boxing is type-directed in Rust, dynamic-only in pure-Simple.**
   Rust's `BinOp::Eq | Is | NotEq` lowering boxes whichever operand's STATIC
   HIR type is NOT `Any` whenever the OTHER operand's static type IS `Any`
   (`lowering_expr_ops.rs:123-134` — `left.ty == TypeId::ANY || right.ty ==
   TypeId::ANY`), so `ai == 42` boxes the literal `42` to match `ai`
   regardless of any runtime tracking. Pure-Simple's Binary-op lowering
   (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:2880-2887`) only
   boxes the other operand for the NIL-comparison special case
   (`self.nil_locals.contains(...)`) — there is no general "one side is
   `is_runtime_value_local`, box the plain-literal other side" rule, and no
   HIR-type-directed check at all. Net effect: after the storage-side fix,
   `ai` (now correctly boxed to `42<<3`) compared against a bare literal `42`
   (never boxed, since it is not itself Any-typed or an Any-param call arg)
   very likely still evaluates `336 == 42 -> false`, not `true`.
2. **`.to_text()` render path does not check `is_runtime_value_local`.**
   `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2531-2550`
   (`is_text_conversion` in the `Unresolved` method-call arm) decides how to
   render purely from `local_mir_type_of(receiver)` — for a boxed `Any` local
   that MIR type is the erased `I64` (same as any plain int local, since `Any`
   lowers to `MirType.i64()`), so it falls into
   `coerce_concat_operand`/`rt_raw_i64_to_string` and renders the TAGGED bit
   pattern as if it were the raw value (e.g. boxed `42` -> `"336"`, not
   `"42"`). This is the doc's already-noted "quieter" symptom
   (`rt_raw_i64_to_string` instead of `<value:0x..>`); the storage-side fix
   changes WHAT gets fed into this renderer but does not fix the renderer
   itself.

**Not fixed here — out of the prescribed 2-site scope for the 2026-08-06
pass, and each needs its own careful design** (the comparison fix in
particular is a new kind of check — HIR-static-type-directed, not a
`box_runtime_value` call-site copy — so it is not a "small surgical" port of
the existing pattern the way the two storage-side sites were). Needs its own
repro (`ai == 42`, `ai.to_text()` after confirming the storage-side fix
alone via the interpreter-vs-JIT split) and a scoped fix in
`expr_dispatch.spl`'s Binary case and `method_calls_literals.spl`'s
`is_text_conversion` arm.

## Related, still open

- `box_enum_payload_if_needed` (`lowering_expr_call.rs`) routes `TypeId::BOOL`
  through `BoxInt`, which by the tag argument above produces a tagged int, not
  a bool. An enum payload holding a bool should render `"true"`, not `"1"`.
  Not fixed here — it needs its own repro and arm.
