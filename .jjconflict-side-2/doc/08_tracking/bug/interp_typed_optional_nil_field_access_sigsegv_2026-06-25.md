# JIT SIGSEGV: field access on a `nil` receiver (`b.n` where `b` is nil)

**Date:** 2026-06-25
**Status:** RESOLVED 2026-06-25 — null guard added in Cranelift FieldGet/FieldSet codegen.
**Area:** Cranelift JIT codegen (`run`/`-c` path), NOT interpreter / type inference.
**Severity:** crash (SIGSEGV) — was a wild null deref; now a defined trap.

## Decision (2026-06-25): runtime guard is the enforcement layer — no compile-time check for now

A compile-time check that rejects `b.n` on a non-narrowed optional `T?` (forcing
`if b != nil:` or `b?.n`) was investigated and is **blocked**, not declined:

- The only narrowing-aware place to hook is the HM inference `Field` case
  (`src/compiler/30.types/type_infer/inference_expr.spl`, `synthesize_expr`).
- Probing showed `synthesize_expr` fires **0 times** when checking a user file:
  the HM engine is **dormant for user code** because `lower_and_check_impl`
  stubs HIR lowering for non-bootstrap sources (empty HIR → no body inference).
  Syntactic lints run; type-aware ones do not.
- Root prerequisite is therefore un-stubbing the HIR pipeline — see
  [[interp_aot_source_pipeline_stubbed_non_functional_2026-06-25]] — which was
  reverted earlier as too risky (re-exposes the unbounded interpreted-compiler
  bug chain, incl. this very crash).

So the **runtime guard below is the chosen enforcement** until that pipeline work
is scoped separately. A rough blast-radius estimate for the eventual compile-time
check is **~40–283 sites** (heuristic; exact narrowing-aware count needs the
un-stubbed pipeline). A prototype warn-only lint was written, confirmed
unexercisable for the above reason, and reverted (no production-checker change).

## Resolution

Root cause was misdiagnosed below. It is **not** a compile-time type-inference
recursion. It is a JIT codegen bug:

- `b.n` lowers to a plain `FieldGet` (`SIMPLE_TRACE_FIELD_GET=1` →
  `object=VReg(2) byte_offset=0 field_type=i32`), not a vtable dispatch.
- `compile_field_get` (`src/compiler_rust/.../codegen/instr/fields.rs`) masks the
  receiver's tag bits and loads from the pointer with **no null check**. A `nil`
  receiver masks to `0`, so the load faults at address `0x0` (`si_addr=0x0`,
  rip in valid JIT code) → wild SIGSEGV (rc=139).
- It surfaced now only because the JIT was re-enabled (native_profile / rt-symbol
  restore). On builds where the JIT still defers to the interpreter (production
  `bin/simple`, the older release seed — both fail JIT on `rt_len` NULL-jump),
  the interpreter reports the clean `undefined field 'n' on 'nil'` error (rc=1),
  which is why the older build "worked". The interpreter was never the crash site.

**Fix (round 1):** `builder.ins().trapz(obj_ptr, TrapCode::unwrap_user(12))` before the load
(FieldGet) and store (FieldSet). A nil receiver now hits a defined trap (rc=132,
the compiled-code analogue of a panic on nil access) instead of a wild memory
deref. Verified: repro no longer rc=139; non-nil and nested struct field
get/set still work (`Box(n:42).n` → 42, nested `l.a.x` → 3).

**Fix (round 2 — diagnostic):** the bare `trapz` lowered to `ud2`, so the program
died with a *message-less* SIGILL ("Illegal instruction (core dumped)"), giving the
user no idea why. Replaced both `trapz` calls with `guard_nonnull_receiver()`: it
branches on the nil receiver, prints `runtime error: field access on nil receiver`
to stderr via `rt_eprintln_str` (a codegen-root runtime symbol, always available),
then traps. The crash is still a deterministic trap (rc=132 — `rt_exit` has no
confirmed JIT symbol binding, so a clean exit code was deliberately not chased),
but it now carries a clear diagnostic. Verified 2026-06-25: nil `b.n` read and
`val x = b.n` both print the message then trap; `Box(n:42).n` → 42, write+read
`b.n = 99` → 99 unaffected; nil `b.n = 5` is caught earlier at the semantic layer
(rc=1, "cannot assign field on non-object value").

**Related logic bug — FIXED (interpreter) 2026-06-25:** typed optionals
(`i32?`, `text?`, ...) mishandled the Option API. Root cause: `cast_value` for
`Type::Optional` wrapped the value in `Value::Enum{Option, Some}`, violating the
interpreter's bare-payload convention (`None`=`Value::Nil`, present=bare
payload), so `unwrap_or`/`is_some`/`is_none`/`unwrap` never reached their
handlers. Fix (two sites):
1. `interpreter/expr/casting.rs` — Optional cast now keeps `nil` as `Value::Nil`
   and a present value as its bare payload (no `Some` wrap).
2. `interpreter_method/mod.rs` — the general primitive "method not found" path now
   falls through to `try_bare_some_option_method` (mirroring the Object path), so a
   present *primitive* optional (`mj: i32? = 7; mj.unwrap_or(9)`) gets the Option
   API. Verified: nil→`false/true/5`, present→`7/true/7`; plain `Some`/`None`,
   int/text/dict methods, and genuine unknown-method errors all unaffected.

**STILL OPEN — JIT/native backend (both seed + self-hosted `.spl`; design below).**

### Symptoms (confirmed on both `bin/simple` and the seed, JIT path)
- `mj: i32? = 7; print mj` → `<value:0x7>` (raw untagged int; `rt_value_to_string`
  can't classify it).
- `mj.unwrap_or(9)` / `mj.is_some()` → `Function 'is_some' not found` (method not lowered).
- `a: i32? = 3; a == nil` → **`true`** — value `3` collides with the nil sentinel
  (latent correctness bug). `text?`/pointer optionals work (already tagged).

### Root cause
1. `i32?` resolves to `HirType::Pointer{Shared, inner: I32}` (seed
   `hir/lower/type_resolver.rs:282`), **not** an enum.
2. The Option-method lowering guards
   (`hir/lower/expr/mod.rs:792-867` `lower_builtin_method_call`;
   mirror in `mir/lower/lowering_expr_method.rs:~136`) only fire for
   `HirType::Enum` (`enum_has_variant_for_builtin_method`,
   `enum_payload_type_for_builtin_method` at `hir/lower/expr/mod.rs:57-89`), so a
   `Pointer`-shaped optional falls through → "method not found". `unwrap_or`/
   `unwrap_or_else` aren't lowered for any receiver.
3. The present primitive payload is stored **raw/untagged**, so the type decays to
   `ANY`, `BoxInt` is skipped in the print path (`hir/lower/stmt_lowering.rs:521`),
   and a raw `3` is indistinguishable from `nil`.

### Design (representation = box the primitive payload, mirrors `text?`)
Make a present primitive optional carry a **tagged/boxed** payload (BoxInt =
`value<<3`), nil stays sentinel `3`. Then: prints via `rt_value_to_string`
correctly; `i32?=3` → `BoxInt(3)=24 ≠ 3` (collision gone); `rt_is_some` already
returns `!special || payload!=NIL` so it works on the boxed value.
- **Coerce `T → T?`**: BoxInt primitives at the optional-coercion site (same shape
  as `mir/lower/lowering_expr_call.rs:83` `box_arg_for_any_param`, which already
  boxes for `ANY` params). Pointers/text pass through unchanged.
- **Method dispatch** (add an `Optional`/`Pointer{inner}` arm alongside the enum
  guards): `is_some`→`rt_is_some` (exists), `is_none`→`rt_is_none`,
  `unwrap`→`UnboxInt`/value typed as `inner` (+ optional nil trap reusing the
  `trapz` pattern from `codegen/instr/fields.rs`), `unwrap_or(x,d)`→
  `select(rt_is_some(x), unbox(x), d)`.

### Sites to patch (SEED `src/compiler_rust/…`)
- `hir/lower/expr/mod.rs:792-867` — method dispatch arms (+ `unwrap_or`).
- `hir/lower/expr/mod.rs:57-89` — let helpers see `Pointer`/optional, return inner.
- `mir/lower/lowering_expr_method.rs:~136` — mirror dispatch.
- `mir/lower/lowering_expr_call.rs:83` — box primitive on `T→T?` coercion.
- `codegen/instr/mod.rs` `BoxInt`/`UnboxInt` already exist; reuse.

### Sites to patch (self-hosted `.spl` `src/compiler/…`) — required for `bin/simple`
- `50.mir/_MirLoweringExpr/method_calls_literals.spl` (`lower_method_call`) — method dispatch.
- `20.hir/hir_types.spl:479` already has `Optional(inner)` (richer than the seed's
  `Pointer` decay) — box at its coercion + print path.
- Reaching production needs a **bootstrap rebuild + `--deploy`** (flagged risky in
  `.claude/rules/bootstrap.md`; smoke-test + restore-on-break afterward).

### Verification target
`i32?`/`text?`/`f64?`: `print present` → value; `unwrap_or` → value-or-default;
`is_some`/`is_none` correct; `i32?=3` not nil; enum `Some`/`None`, plain
pointers, and non-optional methods unaffected.

### Workflow outcome 2026-06-25 (3-phase implement→verify→synthesize)

A multi-agent workflow implemented + adversarially verified the SEED design.
Outcome: **seed approach VALIDATED for the common case, but NOT complete; .spl
port structurally blocked.** Seed-only has **zero production value** (production
`bin/simple` is the self-hosted `.spl` compiler; the seed only affects bootstrap),
so nothing was landed or deployed.

**Seed — verified green (let-bound primitive optionals), non-regressive:**
`print` present (`i32?/f64?/text?`) → value (no `<value:0xN>`); `unwrap`/
`unwrap_or`/`is_some`/`is_none` correct; `i32?=3` no longer collides with nil
(payload boxed to `24`). No regression to enums, plain methods, `-c` smoke.
Implementation shape that worked (diffs captured in the workflow run
`wf_81e1ad20-5aa` output; touched `hir/lower/expr/mod.rs`,
`mir/lower/lowering_stmt.rs`, `mir/lower/lowering_expr_builtin.rs`):
`optional_inner_for_builtin_method` (Pointer→inner) gates is_some/is_none/unwrap/
unwrap_or; `unwrap_or` lowered to `HirExprKind::If{is_some, payload, default}`;
`box_for_optional_coercion` BoxInts the primitive payload at `HirStmt::Let`.

**Correctness lens FAILED — remaining gaps (must-fix before "optionals work"):**
1. **Sentinel collision on `0`/`false`**: nil is represented as `0` in this path,
   so `i32?=0` / `bool?=false` (BoxInt(0)=0) still read as nil (`is_some=false`,
   `unwrap_or`→default). Needs a nil representation distinct from a `0` payload
   (unify on tagged sentinel `3`, not `0`).
2. **Coercion wired ONLY at `HirStmt::Let`** — reassignment (`x = 7`), `T?`
   params/returns, and struct-field init flow the primitive RAW → re-trigger
   `<value:..>` + collision. (`fn f() -> i32?` literal-return miscompiles in BOTH
   backends.)
3. **`Some(99)` constructor form** prints `<enum@0x..>` / unwrap garbage (the
   boxed-enum Option path, distinct from primitive `T?`).
4. `bool?` bare `print` shows `1`/`0` (cosmetic; Option semantics correct).
   All four reproduce identically in the interpreter → language-level
   representation issues the native path mirrors, not native regressions.

**`.spl` port — BLOCKED (the real production blocker, larger than this bug):**
the self-hosted MIR has **no `BoxInt` / no primitive value-tagging at coercion at
all** — `val a: any = 9; print a` already prints `<invalid-heap:0x9>` on
production `bin/simple`. A faithful port = implement the tagging primitive
(MIR `Shl`+`BitOr` or a runtime call) + symmetric unbox, wired at every `T→any`
and `T→T?` coercion site, then a stage-2/3 bootstrap verification. Dispatch site
for the method half: `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`
`lower_method_call`, intercept `Optional(inner)` before `match resolution` (~L151).

**Conclusion:** native typed-optional support is a representation/infra *feature*
(unify nil sentinel → fix zero/false; cover all coercion sites; build `.spl`
`any`-boxing), not a localized fix, and the production half can't ship without
the `.spl` boxing infrastructure + a bootstrap deploy. Tracked here for a
dedicated effort; deploy stays human-gated.

---

> The analysis below is the ORIGINAL report; its "compile-time recursion" theory
> is incorrect (kept for history; corrected by the Resolution above).

## Repro (minimal)

```simple
struct Box:
  n: i32

fn main():
  val b: Box? = nil
  print "{b.n}"      # SIGSEGV (rc=139), no output at all
```

Run with `src/compiler_rust/target/bootstrap/simple run repro.spl`.

## Key observations (isolation)

- **Plain `nil` is fine.** `val x = nil; print "{x.n}"` → clean error
  `undefined field 'n': cannot access field on value of type 'nil'` (rc=1).
  Handled by the `_ =>` arm in `interpreter/expr/calls.rs:862`.
- **Only the type annotation differs.** The crash needs the receiver declared as
  an *optional struct* type (`Box?`). The runtime value is plain `nil`:
  `val b: Box? = nil; print "b is {b}"` prints `b is nil` and `b.?` is `false`
  (rc=0). So `b` evaluates to `Value::Nil`, yet `b.n` crashes only because of the
  `Box?` declared type.
- **The crash is at compile time, not runtime.** The failing run produces *zero*
  output (1-line log = only the shell's "Segmentation fault" line); the
  `[DEBUG FIELD ACCESS]` eprintln at `calls.rs:864` never fires. So the segfault
  happens during type inference / HIR lowering of the `b.n` access on an optional
  struct type — before the interpreter ever evaluates the field access.
- **No panic / no "stack overflow" message** → either deep type-inference
  recursion that faults the guard page silently, or a genuine bad deref.

## Regression window

- Works on the older Rust seed `src/compiler_rust/target/release/simple`
  (built 2026-06-23): the related program `nil.unwrap_or(Box(n:99))` then `.n`
  prints `ok 99` (rc=0).
- Crashes on a fresh `--profile bootstrap` build of the **current** seed source
  (2026-06-25). So a seed change landed between 2026-06-23 and 2026-06-25
  regressed optional-struct field-access type resolution into an infinite
  recursion / segfault. NOT introduced by this session's work (reproduced on a
  baseline build with no local seed edits).

## Related (same area, likely same root)

- `val mi: i32? = nil; mi.unwrap_or(5)` returns **`nil`** instead of `5`
  (typed-optional `nil` does not reach the `Value::Nil` Option arm at
  `interpreter_method/mod.rs:1064`; it is routed through a typed path that
  returns nil). Logic bug, no crash on its own — but feeding the wrong `nil`
  result into a field access is how the SIGSEGV above is reached in real code.

## Suspected root cause

The interpreter resolves `recv.field` using the receiver's *declared* type. For
an optional struct `T?` it appears to recurse through the optional/inner type
without a base case when the value is `None`/`nil`. Compare the inference
`enum Type` (`src/compiler/20.hir/inference/types.spl`): `Optional(inner: Type)`
is self-referential; a missing terminator on the `Optional` case during
field-type resolution would recurse forever.

## Suggested fix direction (unverified)

1. In the field-type resolution path, when the receiver type is `Optional(inner)`,
   resolve the field against `inner` exactly once (auto-unwrap), with an explicit
   recursion guard / depth bound so a cyclic optional type cannot loop.
2. Ensure a typed-optional `nil` value is `Value::Nil` end-to-end so it reaches
   the `Value::Nil => None` Option handling (fixes the `unwrap_or` returning-nil
   logic bug above too).
3. Add a runnable guard test (`b: T? = nil; b.field`) that must produce the same
   clean `undefined field … on 'nil'` error as plain `nil`, never a segfault.
