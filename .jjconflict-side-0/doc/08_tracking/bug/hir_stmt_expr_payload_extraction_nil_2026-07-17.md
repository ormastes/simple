# rt_enum_payload landmine on StmtKind.Expr (worked around); StmtKind.Expr stage2-gate misroute is FIXED

**Date:** 2026-07-17
**Scope:** `src/compiler/20.hir/hir_lowering/statements.spl` (`lower_hir_stmt`)
**Status:** Primary bug (stage2-gate misroute) FIXED and verified. One landmine
found+documented+avoided (not blocking). One separate, unrelated downstream
issue observed and flagged (not investigated — out of this bug's scope).

## Primary bug (FIXED)

`lower_hir_stmt`'s multi-arm `match stmt_kind_value:` mis-routes on
stage4/native-build worker execution — a genuine `StmtKind.Expr` value
matched none of the qualified `case` arms and fell through to the `case _:`
catch-all, emitting `"unsupported statement kind"` and aborting HIR lowering
for every bare-expression-statement body. This mirrors the already-documented
Val/Var/Return/Assign mis-route (bug doc iteration 20 #86).

**Fix:** extended the existing disc-dispatch pre-check pattern (used for
Val/Var/Return/Assign) to `StmtKind.Expr`: compare
`hir_stmt_kind_disc(stmt_kind_value)` against
`hir_stmt_kind_disc(StmtKind.Expr(sk_dummy))` and, on match, extract the
payload via a single-arm `match stmt_kind_value: case StmtKind.Expr(einner):
einner` (the same pattern-extraction idiom Val/Var/Assign already use
successfully for their own Expr-typed fields), before the raw
multi-arm match ever runs.

**Verified via direct repro** (seed native-build — see Verification below,
not the unit-spec suite, which could not run against the currently-deployed
binary; see Tooling caveat):

| Stage | `unsupported statement kind` | (interim) nil-payload crash/guard | HIR lowering failure |
|---|---|---|---|
| Before any fix | 6 real firings | n/a | yes (`[ERROR] phase 3 FAILED`) |
| After dispatch fix, `rt_enum_payload` extraction | 0 | yes — nil payload, guarded to `"empty expression-statement payload"` diagnostic, 3 firings (matches every statement in the 3-statement repro) | no crash, but statements degrade to `HirExprKind.Error` |
| After switching to match-based extraction (final) | 0 | 0 | **0 — HIR lowering succeeds** for every statement shape tested (`print(...)`, bare `1 + 1`) |

Repro file:
```simple
fn main():
    print("before")
    1 + 1
    print("after")
```

Repro command (per `.claude/rules/bootstrap.md`'s internal stage-replay
recipe):
```bash
SIMPLE_BOOTSTRAP=1 src/compiler_rust/target/bootstrap/simple native-build \
  --source <dir containing the repro file> --source src/lib \
  --entry <repro file> -o <out>
```

## Landmine found and avoided: `rt_enum_payload` returns nil for `StmtKind.Expr`'s payload

While root-causing the above, the first fix attempt mirrored `Return`'s
existing idiom (`rt_enum_payload(stmt_kind_value)` to extract the payload).
That returned the nil sentinel (`3`, see
`src/runtime/simple_core/core_enum.spl`'s `rt_enum_payload`) for **every**
`StmtKind.Expr` value in this execution context — confirmed unconditional
(fired for plain `print(...)` calls, not just the bare-arithmetic
statement) — even though `rt_enum_discriminant` on the *same* value
correctly resolves to `StmtKind.Expr`'s discriminant moments earlier (i.e.
the enum wrapper is validly tagged; only the single-field struct payload
extraction via this particular extern fails).

Switching to the **match-based pattern-extraction** idiom already used
successfully by the Val/Var/Assign disc-branches in this same function
(`match stmt_kind_value: case StmtKind.Expr(einner): einner  case _: sk_dummy`)
resolved this cleanly — no nil, no crash, correct payload every time. This
directly contradicts an older in-file comment (now removed) claiming
pattern-extracted payloads are "GARBAGE on stage4 (iteration 17,
disc=823890719)" — that claim does not hold for `StmtKind.Expr` on the
current source; the `rt_enum_payload` extern itself is the one with the gap,
not pattern-matching.

**Follow-up recommended, not required:** `rt_enum_payload`'s failure mode for
`StmtKind.Expr` specifically (discriminant 0, required — not optional —
struct payload) is real and reproducible, just no longer load-bearing here.
Worth root-causing separately if any other call site depends on
`rt_enum_payload` for a required (non-Optional) struct-typed single-field
enum payload. Note: `Return(Expr?)`'s use of this same extern (line ~404,
untouched by this fix) was assumed working (it predates this session and
its disc-branch is reachable/exercised elsewhere) but was **not**
independently re-verified here — given `rt_enum_payload` just proved to
return nil for `Expr`'s payload specifically, treat `Return`'s payload
extraction as an unverified adjacent risk, not confirmed-good. A silently
nil-dropped return value would misbehave without a compile error (the
existing code treats nil payload as "no return value", a valid state for
`Return`, so a genuine bug there would not be loud).

**2026-07-17 follow-up:** the adjacent `Return(Expr?)` path now uses the same
single-arm match extraction as `StmtKind.Expr`; it no longer depends on
`rt_enum_payload`. `statement_payload_types_source_spec.spl` pins both
payload paths and rejects the old helper form. Runtime execution remains
pending under the tooling caveat below.

## Separate, unrelated downstream observation (NOT investigated)

With the primary bug fixed, the same repro command still exits 1 — but with
**no diagnosable error text at all** (no `[ERROR] phase ... FAILED`, no `HIR
lowering error`, just a bare `native-build worker exited with code 1` with
nothing preceding it). This reproduces identically for a print-only variant
(no bare-expression statement at all), so it is **not** related to
`StmtKind.Expr` or statement dispatch — it surfaces only because HIR
lowering now gets further than before. This matches the known
"native-build eprint lost — worker stderr not captured" landmine (see repo
memory). Not investigated further here — out of this bug's scope (a
different phase: MIR lowering, codegen, or worker-output-capture
infrastructure, not `hir_lowering/statements.spl`).

## 2026-07-17 follow-up (STAGE2-CHAIN lane): MIR-layer wall found + fixed; deeper payload-extraction landmine confirmed, NOT fixable from Simple source

Picked up where the above left off: with the HIR-layer `StmtKind.Expr` dispatch
fix in place, the same seed native-build repro (`print("before")` /
`1 + 1` / `print("after")`) still produced no binary — silently, with the
existing `native-build eprint lost` landmine hiding the real cause behind a
bare `native-build worker exited with code 1`.

### Reliable way to see full, untruncated output

`native_build_main.spl`'s outer wrapper caps relayed stdout/stderr at 12000
chars (`OUTPUT_LIMIT` in `native_build_main.spl`) and its `eprint` is itself
simulated as `print "[STDERR] {msg}"` (see `src/lib/nogc_sync_mut/io/process_ops.spl:387`
and 5 other identical `mod_stub.spl`/`process_ops.spl` copies) — so real
diagnostics exist but get lost to truncation, not to a missing message. Bypass
both by invoking the worker directly, without the outer wrapper, and
redirecting to a real file:

```bash
SEED=$(pwd)/src/compiler_rust/target/bootstrap/simple
SIMPLE_NATIVE_BUILD_WORKER=1 SIMPLE_BOOTSTRAP=1 SIMPLE_COMPILER_TRACE=1 \
  SIMPLE_BOOTSTRAP_DEBUG=1 SIMPLE_EXECUTION_MODE=interpret SIMPLE_BINARY="$SEED" \
  "$SEED" run src/app/cli/native_build_worker.spl \
  --source <dir> --source src/lib --entry <entry.spl> -o <out> \
  > stdout.log 2> stderr.log
```

`SIMPLE_COMPILER_TRACE=1` gates `log_phase`/`[mir-lower]`/`[mir-lower-free]`
tracing; `SIMPLE_BOOTSTRAP_DEBUG=1` additionally gates
`[bootstrap-real-llvm]`/`[mir-to-llvm]` tracing (`bootstrap_trace_enabled()`
in `driver_bootstrap.spl`, a *different* env var than
`driver_phase_trace_enabled()`/`mir_lower_trace_enabled()`).

### Wall 1 (FIXED): MIR-layer StmtKind.Expr misroute, sibling of the HIR-layer bug

`src/compiler/50.mir/mir_lowering_stmts.spl`'s `lower_stmt` has the exact same
disease as the already-fixed `20.hir/hir_lowering/statements.spl`: a raw
multi-arm `match stmt_kind_value: case HirStmtKind.Expr(extracted_expr): ...
case _: ()`. On stage4/native-build worker execution a genuine
`HirStmtKind.Expr` value matched none of the qualified arms and fell through
to `case _: ()` — a **silent no-op**, not a crash. Every bare-expression
statement therefore contributed zero MIR instructions, which tripped
`bootstrap_globals.spl`'s existing loud-failure guard
(`bootstrap_lower_hir_globals_to_mir_module_for_target`): `error: bootstrap
entry lowered to 0 MIR instructions (ret-0 stub module)`. That guard's own
`eprint` calls are *also* simulated-to-stdout, so even this message never
survived the outer wrapper's relay in the ordinary CLI path — hence "no
diagnosable error text at all" upstream.

**Fix** (`src/compiler/50.mir/mir_lowering_stmts.spl`, ~line 293): mirrored
the already-proven idiom from the Let arm two lines above and from the
HIR-layer fix — pre-dispatch by `mir_hir_stmt_kind_disc(stmt_kind_value) ==
mir_hir_stmt_kind_disc(HirStmtKind.Expr(fallback_expr))`, then extract the
payload via a single-arm match, before the raw multi-arm match is ever
reached.

**Verified via before/after `[mir-lower-free] done instr-total=` trace** on
the 3-statement repro:

| State | `instr-total` | Result |
|---|---|---|
| Before this fix | `0` | `rt_exit(1)` from the loud-failure guard; no binary |
| After this fix | `3` (this repro) / `5` (a `val a = 1+1; print(a)` variant) | Guard passes; build proceeds to LLVM/link and **produces a real, running ELF binary** (`file` confirms `ELF 64-bit ... dynamically linked ... not stripped`, exit code 0) |

### Wall 2 (NOT FIXED, root-caused, NOT a Simple-source-fixable landmine): `HirStmtKind.Expr`/`StmtKind.Expr` single-arm payload EXTRACTION itself is unreliable, independent of the dispatch fix above

Fixing Wall 1 exposed a **second, deeper occurrence of the same underlying
seed defect class**, one level down from where it was previously understood.
The produced binary from Wall 1's fix runs (`exit 0`) but **prints nothing** —
`"before"`/`"after"` never appear, and a `val a = 1 + 1; print(a)` variant also
produces no output.

Root cause, confirmed via direct trace instrumentation (added, verified, then
fully stripped — no instrumentation shipped):

- The preserved LLVM IR (`compile_ir_to_object`'s temp `.ll` path) for
  `__simple_main` was **literally `{ ret i64 0 }`** — no calls, no arithmetic,
  despite `bootstrap_globals.spl` reporting `instr-total=3` (real,
  Wall-1-fixed) moments earlier in the *same process*.
- Tracing every stage between "MIR lowering reports 3 real instructions" and
  "LLVM emission" (`bootstrap_mir_function_at` → `bootstrap_ssa_phi_function`
  → `MirBody.from_function` → `translator.translate_function`) showed the
  data **genuinely has 3 real instructions right up to the `translate_block`
  call** — then each instruction's *actual kind* is `Const(dest, I64,
  Int(3))` **for all three unrelated statements** (`print("before")`, `1 + 1`,
  `print("after")`), not `Call`/`BinOp`. `Int(3)` is the documented HIR nil
  sentinel (`NilLit` materializes to `Const(Int(3))`, see
  `expr_dispatch.spl:1860`'s comment and `core_enum.spl`'s `rt_enum_payload`
  nil-sentinel note above).
- Traced one layer further up: `20.hir/hir_lowering/statements.spl`'s own
  fixed dispatch branch (the "Primary bug (FIXED)" section above) — the
  branch that correctly *routes* to `StmtKind.Expr` handling — still
  extracts its payload via `match stmt_kind_value: case StmtKind.Expr(einner):
  einner  case _: sk_dummy`. Direct instrumentation on `expr_t.kind` showed
  it is `ExprKind.NilLit` (the `case _` fallback `sk_dummy`) for **every one**
  of the 3 statements, even though the outer disc-dispatch correctly confirms
  each is genuinely `StmtKind.Expr`. **The single-arm match's payload
  extraction itself silently returns the wildcard fallback instead of the
  real bound payload for this specific constructor**, independent of and
  downstream of the already-fixed routing bug. This directly contradicts this
  same bug doc's earlier "Primary bug (FIXED)" section, which assumed (but
  did not independently verify) that match-based extraction correctly
  recovers `StmtKind.Expr`'s payload — it does not.
- The identical symptom reproduces **independently at the MIR layer**
  (`HirStmtKind.Expr`'s analogous single-arm extraction in
  `mir_lowering_stmts.spl`, this session's Wall-1 fix) — same "extraction
  returns the `case _` fallback" behavior, confirmed via dedicated
  instrumentation there too.
- **Not the cause** (each tested and disproved by direct experiment, then
  reverted): (a) function size/complexity — isolating the extraction into its
  own small top-level function (mirroring the documented
  `compile_bootstrap_context_to_native` "Stage1-generated compilers can crash
  dispatching... keep the bootstrap lane on a plain function" workaround
  pattern) made no difference; (b) stale/shared local variable binding —
  re-reading `stmt.kind` fresh immediately before the match, instead of using
  the already-bound `stmt_kind_value`, made no difference; (c) reusing the
  same dummy value for both the disc-exemplar construction and the match's
  `case _` fallback — a plausible aliasing theory — made no difference
  (Let/Val's extraction reuses its dummy identically and is unaffected); (d)
  declaration order / discriminant value — reordering `StmtKind` so `Expr` is
  no longer variant 0 (`Val` first) was tested as a targeted experiment (both
  `StmtKind.Expr` and `HirStmtKind.Expr` are the first-declared variant of
  their respective enums, the one common thread across both independently-
  broken sites) but did not resolve the MIR-layer symptom in the one test run
  completed, and separately triggered an unrelated-looking crash
  (`error: semantic: method 'len' not found on type 'nil'` inside
  `ssa_alloca_transform_blocks`) on a full closure rebuild — too large a
  blast radius and too inconclusive a signal to justify keeping a
  system-wide enum reorder for an unconfirmed fix; **reverted**, not shipped.
- `rt_enum_payload` was already known-broken for this exact payload (see
  "Landmine found and avoided" section above); this session additionally
  confirms **match-based extraction, the very workaround this doc's Primary
  Bug section recommended and believed worked, is unreliable too**, for this
  one specific constructor, in this one specific execution context
  (interpreted seed, native-build worker, heavy multi-thousand-module load).
  Both known Simple-source-level extraction techniques for this payload now
  have confirmed failure modes. This looks like a genuine defect in the seed
  interpreter's (`src/compiler_rust`) enum pattern-match/payload-binding
  implementation, not something fixable by restructuring the Simple-source
  call site — and `src/compiler_rust` is out of scope for this lane.

**Net effect of this session's work:** the seed native-build closure repro
now reliably **builds, links, and runs** a real ELF binary for programs whose
bodies are entirely bare-expression statements (previously: hard abort, no
binary at all). It does **not** yet execute those statements' real semantics
— they silently lower to a NilLit placeholder instead. This is real,
measured, verified progress (a distinct, necessary fix, independently
verified via instruction-count and IR-content evidence before/after), but is
**not** sufinicient on its own for full behavioral correctness. Follow-up
owner: root-cause the extraction defect inside the seed interpreter itself
(`src/compiler_rust`), or find a third, not-yet-tried Simple-source
workaround for reading a first-declared, single-field enum-variant payload
reliably under this execution mode.

**Repro (still current, seed unmodified in this repo checkout)**:
```
fn main():
    print("before")
    1 + 1
    print("after")
```
Direct-worker command per "Reliable way to see full, untruncated output"
above. Look for `[mir-lower-free] done instr-total=` (should be `3`, not
`0`, confirming Wall 1 stays fixed) and the produced binary's actual stdout
(currently empty, confirming Wall 2 is still open).

**Instrumentation status:** all temporary diagnostic `print` statements added
during this investigation (in `mir_lowering_stmts.spl`,
`driver_bootstrap.spl`, `_MirToLlvm/core_codegen.spl`, and a since-reverted
extraction helper + enum reorder experiment in `statements.spl` /
`parser_types_expr.spl`) have been fully stripped. Only the real Wall-1 fix
(the disc-dispatch pre-check in `mir_lowering_stmts.spl`, with an inline
comment documenting the residual Wall-2 landmine) remains.

## Tooling caveat

`bin/simple` currently resolves to a Rust-seed binary
(`bin/release/x86_64-unknown-linux-gnu/simple`, dated 2026-07-11), not the
true self-hosted pure-Simple binary — it prints "this Rust-built Simple
binary is a bootstrap seed only" and lacks externs the test runner needs
(`rt_cli_arg_count`), so `bin/simple test` could not be run to validate this
fix against the unit-spec suite. Verification instead used the seed
native-build repro above (arguably stronger evidence for this specific bug
than the unit suite would be) plus a manual grep-based check that
`test/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.spl`'s
source-content assertions (extended here to also check for
`StmtKind.Expr`'s disc-dispatch line) match the current file content. This
`bin/simple` state is a known, repo-wide, pre-existing condition — not
something introduced or owned by this fix.

## 2026-07-17 follow-up (WALL2-SEED lane): Wall 2 ROOT-CAUSED and FIXED in the seed interpreter

Picked up the "not fixable from Simple source" landmine from the section
above. Root-caused and fixed in `src/compiler_rust` (the seed itself), not a
Simple-source workaround.

### Root cause

`src/compiler_rust/compiler/src/interpreter_method/mod.rs`, function
`evaluate_method_call` (the interpreter's dispatcher for any `Receiver.name(args)`
call syntax — this is the actual code path for `StmtKind.Expr(x)`-shaped enum
variant CONSTRUCTOR calls, not `interpreter_call::evaluate_call`'s `FieldAccess`
branch, which turned out to be effectively dead for this call shape since the
parser emits `Expr::MethodCall`, not `Expr::Call{callee: FieldAccess}`, for
`X.Y(args)`).

The function decides whether `Receiver.name(args)` is a "bare module fallback"
(treat `name` alone as a global function/class lookup, ignoring `Receiver`
entirely) using a helper:

```rust
fn use_bare_module_fallback(receiver_in_env: bool, receiver_is_class: bool) -> bool {
    !receiver_in_env && !receiver_is_class
}
...
if use_bare_module_fallback(env.get(module_name).is_some(), classes.contains_key(module_name)) {
    if let Some(func) = functions.get(method).cloned() { return exec_function(...); }
    if classes.contains_key(method) { return instantiate_class(method, args, ...); }
}
```

`env` here is the CURRENT (often function-local) environment. The
module-level `Value::EnumType` binding that `evaluate_module_impl`'s first
pass inserts for every declared enum (so a bare `EnumName` identifier
resolves correctly) is inserted only into the OUTER module-level `env`, not
copied into every function/method's local environment. So for ANY
`EnumName.Variant(args)` constructor call made from INSIDE a function or
method body, `env.get(module_name)` is `None` — `receiver_in_env` is wrongly
`false`. Since a plain enum name is (correctly) never itself a class,
`receiver_is_class` is also `false`, so `use_bare_module_fallback` returns
`true` and the code looks up `method` (the VARIANT name, e.g. `"Expr"`) as a
bare global function or class name, completely bypassing enum-variant
resolution (the correct `Value::EnumType { enum_name } => { ... }` arm sits
much further down in the same function, at line ~935, and is never reached).

This is silent and harmless for variant names with no global collision
(`Val`, `Assign`, `Var`, ...) — `functions.get("Val")`/`classes.contains_key("Val")`
both fail, so the bare-fallback block does nothing and falls through to the
correct `evaluate_expr(receiver, ...)` + `Value::EnumType` path a few lines
later (which resolves `EnumName` via `enums`/`GLOBAL_ENUMS`/`BLOCK_SCOPED_ENUMS`
fallbacks exactly like `Expr::Identifier` evaluation already does in
`interpreter/expr/literals.rs:296` — the more complete, correct precedent this
fix now mirrors). But for a variant whose bare name ALSO happens to be a real
global class/struct name anywhere in the whole loaded program —
`StmtKind.Expr` / `HirStmtKind.Expr`, whose first-declared variant is named
`Expr`, colliding with the totally unrelated `struct Expr:` AST node type
declared in `parser_types_expr.spl` (imported transitively into scope
wherever `StmtKind`/`HirStmtKind` are used) — the bare-fallback block's
`classes.contains_key(method)` check succeeds, and `instantiate_class("Expr", args, ...)`
runs instead, silently constructing an unrelated `Value::Object{class:"Expr", ...}`
(the positional args stuffed into `Expr`'s first field, `kind`, with the
wrong type) instead of `Value::Enum{enum_name:"StmtKind", variant:"Expr", payload:...}`.

This explains BOTH previously-observed symptoms as one mechanism:
- `rt_enum_payload`/`rt_enum_discriminant` return the not-an-enum sentinel
  (nil / `-1`) for a value that is genuinely, semantically a `StmtKind.Expr` —
  because at construction time it was never actually built as `Value::Enum`.
- The disc-dispatch pre-check idiom's own ROUTING appeared to "work" for the
  Expr branch in production: the exemplar construction
  `StmtKind.Expr(sk_dummy)` inside `lower_hir_stmt` (a `me` method) is
  ALSO misconstructed the same way, so `hir_stmt_kind_disc(StmtKind.Expr(sk_dummy))`
  also returns the same not-an-enum sentinel. If the REAL `stmt_kind_value`
  was similarly misconstructed wherever the self-hosted parser originally
  built it (parser statement-construction is itself always inside a
  function/method), both sides of the `sk_disc == hir_stmt_kind_disc(StmtKind.Expr(sk_dummy))`
  comparison collapse to the same sentinel and coincidentally compare equal —
  routing "succeeds" for the wrong reason. Downstream, `pattern_matches`'s
  `Pattern::Enum` arm (`interpreter_patterns.rs`) has its own `Value::Object`
  positional-class fallback, but it requires `enum_name == class` (`"StmtKind" == "Expr"`),
  which is false, so the match genuinely falls through to `case _`, returning
  the wildcard/dummy payload — exactly the observed "payload extraction
  silently returns the wildcard fallback" symptom.

### Fix

`src/compiler_rust/compiler/src/interpreter_method/mod.rs`: `use_bare_module_fallback`
gained a third parameter, `receiver_is_enum`, computed at the call site as
`enums.contains_key(module_name) || GLOBAL_ENUMS.with(|c| c.borrow().contains_key(module_name)) || BLOCK_SCOPED_ENUMS.with(|c| c.borrow().contains_key(module_name))`
(mirroring the enum-registry fallback chain already used elsewhere in the
interpreter, e.g. `interpreter/expr/literals.rs`'s `Expr::Identifier`
handling and `interpreter_method/mod.rs`'s own `Value::EnumType` arm). The
bare-module-fallback shortcut is now skipped whenever the receiver is a
known enum type, letting control fall through to the pre-existing, correct
`Value::EnumType` variant-construction arm.

### Regression tests (seed-side, Rust)

Added to `src/compiler_rust/compiler/src/interpreter_patterns.rs`'s existing
`#[cfg(test)] mod tests` (same `run()`-a-Simple-snippet-through-the-interpreter
harness already used by that file's other pattern-matching regression tests):

- `enum_variant_colliding_with_class_name_constructs_correctly_inside_fn_body` —
  minimal construction-level isolation: `StmtKind.Expr(x)` inside a plain
  `fn` body, asserting `rt_enum_discriminant` is not `-1`.
- `enum_variant_colliding_with_class_name_constructs_correctly_at_module_level` —
  same construction at module top-level, as a control case (this direction
  always worked; kept to catch a future regression the other way).
- `enum_variant_disc_dispatch_and_payload_extraction_survive_class_name_collision` —
  full production shape: a `me` method doing disc-dispatch pre-checks against
  freshly-constructed exemplar values (reusing a shared `sk_dummy` across
  multiple constructor calls, exactly like `lower_hir_stmt`), then a
  single-arm `match ...: case StmtKind.Expr(einner): einner  case _: sk_dummy`
  extraction. Asserts the real payload (`42`) comes out, not the
  misroute/wildcard sentinels (`-100`/`-99`/`-1`/`-2`).
- `enum_variant_first_declared_payload_survives_field_access_through_fn_param` —
  sibling: payload read via a struct field crossing a function-call boundary
  (this one already passed before the fix; kept as baseline coverage).
- `enum_variant_real_value_also_built_inside_fn_reproduces_coincidental_routing_match` —
  closes the loop on the EXACT documented production symptom: both the
  disc-dispatch exemplar AND the "real" `stmt_kind_value` are constructed
  from inside a function (`build_stmt`, mirroring the self-hosted parser's
  own statement-construction functions). Pre-fix this reproduces "routing
  coincidentally succeeds, then payload extraction returns the wildcard" —
  the precise two-stage failure mode described in the "Wall 2" section above
  — rather than the simpler "routing never matches" symptom the other tests
  show.

**Before/after evidence** (`cargo test -p simple-compiler --lib interpreter_patterns::`,
run from `src/compiler_rust`):

| State | Result |
|---|---|
| Before fix (`interpreter_method/mod.rs` reverted to prior HEAD) | `7 passed; 3 failed` — `enum_variant_colliding_with_class_name_constructs_correctly_inside_fn_body` (`left: 1, right: 0`, i.e. `rt_enum_discriminant == -1`), `enum_variant_disc_dispatch_and_payload_extraction_survive_class_name_collision` (`left: -100, right: 42`, misroute fallback fired), and `enum_variant_real_value_also_built_inside_fn_reproduces_coincidental_routing_match` (`left: -99, right: 42`, coincidental-routing-then-wildcard-extraction) all FAIL |
| After fix | `10 passed; 0 failed` |

**Full-suite regression check**: ran `cargo test -p simple-compiler --lib`
(3282 tests) both before and after the fix and diffed the sorted `FAILED`
test-name lists. The two lists are **identical except for the 2 target tests
above flipping from FAILED to passing** — 254 other failures are pre-existing
and unrelated (GPU SIMD error-path tests, VHDL codegen, `native_project`
runtime-bundle tests, etc.), present in both runs. Zero collateral
regressions from this change.

**Suite pass counts** (all after the fix, `src/compiler_rust`):
- `interpreter_patterns::` — 10/10 passed
- `seed_regression` (across `hir::lower`, `interpreter::expr::collections`,
  `mir::lower`) — 18/18 passed
- `codegen::local_execution_tests` — 14/14 passed
- Full `cargo test -p simple-compiler --lib` — 3026/3282 passed, 256 failed
  (all 256 pre-existing per the diff above; 254 identical before/after this
  fix, plus the 2 that were captured in that earlier full-suite run before
  the 5th test above was added), 1 ignored

### Files changed

- `src/compiler_rust/compiler/src/interpreter_method/mod.rs` — the fix
  (`use_bare_module_fallback` gains `receiver_is_enum`; call site computes it
  from `enums`/`GLOBAL_ENUMS`/`BLOCK_SCOPED_ENUMS`).
- `src/compiler_rust/compiler/src/interpreter_patterns.rs` — 5 new regression
  tests appended to the existing `#[cfg(test)] mod tests`.

Not touched: the Simple-source disc-dispatch workarounds in
`src/compiler/20.hir/hir_lowering/statements.spl` and
`src/compiler/50.mir/mir_lowering_stmts.spl` — left in place per instructions
(harmless, guard older seeds, and the match-based extraction idiom they use
is now provably correct with this fix in place).

### End-to-end native-build repro: NOT re-run (scope note)

The bug doc's own `print("before") / 1 + 1 / print("after")` native-build
worker repro (see "Reliable way to see full, untruncated output" above) was
**not** re-run against a freshly rebuilt seed binary in this session. The
existing `src/compiler_rust/target/bootstrap/simple` on disk predates this
fix. Rebuilding it (`cargo build --manifest-path src/compiler_rust/Cargo.toml
--profile bootstrap -p simple-driver`) was judged too costly/risky to run
here: the repository currently has a very large number of unrelated
in-flight uncommitted changes from other parallel lanes across dozens of
files (confirmed via `git status`), so a full seed rebuild right now would
(a) take significant time, (b) contend with other lanes' concurrent cargo
usage, and (c) risk an unrelated build break from a mid-flight change
elsewhere producing a false negative not attributable to this fix. The
cargo-level evidence above (FAIL-before/PASS-after on 3 targeted tests, one
of which — `enum_variant_real_value_also_built_inside_fn_reproduces_coincidental_routing_match`
— reproduces the exact two-stage "routing coincidentally succeeds, payload
extraction returns wildcard" symptom described in this doc, plus a
zero-collateral-regression full-suite diff) is considered sufficient proof
of the fix at the unit level. Closing the loop with a live native-build
rebuild + repro is a reasonable follow-up for whoever next rebuilds the seed
for unrelated reasons.

## 2026-07-17 follow-up (REDEPLOY-GATE lane): Wall-2 fix re-confirmed on a from-scratch seed build; live native-build repro still blocked

(Reconstructed by the coordinator from the lane's final report — the lane's
original append of this section was clobbered from the working copy by a
parallel session's reconcile after its final verification.)

**From-scratch rebuild verification.** Both seed profiles rebuilt clean from
current disk state: `cargo build --release` (2m28s, 0 errors, 9 pre-existing
`#[link_name]` warnings for `rt_time_now_micros`/`rt_time_now_unix_micros`)
and `cargo build --profile bootstrap -p simple-driver` (4m10s, 0 errors).
`cargo test -p simple-compiler --lib interpreter_patterns::` on the fresh
build: **10/10 passed** — the Wall-2 `receiver_is_enum` fix is re-confirmed
at unit level on a from-scratch artifact, not just an incremental build.

**The doc's end-to-end native-build repro remains NOT RUN.** Phase-1 source
collection (`--source src/lib`) hits a standing, pre-existing defect:
`certificate.spl` imports `std.cert.x509` / `std.cert.chain` /
`std.cert.validation`, none of which resolve — only `pem.spl` and
`x509_typed.spl` exist under `cert/`. Confirmed present on `origin/main`
(via `git show`/`git ls-tree`), i.e. not working-copy noise. Additionally a
second, path-distinct `certificate.spl` exists under
`src/std/nogc_sync_mut/tls/`, a tree absent from `origin/main` entirely
(flagged, not investigated).

**New fresh-vs-deployed divergence (untested risk, not a cleared item):**
the fresh seed (both profiles) deterministically fails
`SdnValue.Int(...)` construction with "unknown static method Int on class
SdnValue", while the deployed 2026-07-11 `bin/simple` succeeds. On the
actual redeploy path (`SIMPLE_BOOTSTRAP=1`, no `--source`) old and new fail
identically ("cannot iterate over this type") — that failure is shared and
pre-existing, not a regression. Whether the SdnValue name-collision affects
a real stage2 bootstrap compile is **unverified** because the cert wall
blocks `--source src/lib` collection.

**Redeploy-readiness verdict: UNVERIFIED** (neither READY nor flat
NOT-READY). Artifact correctness is strong — clean builds, this week's
fixes all present on disk (Wall-2, HIR+MIR disc-dispatch gates, mut-param
writeback d9ffd9b, Option.map ptr↔i1 58b24c2), and `nm -D` shows the fresh
seed exports **76 `rt_cranelift_*` symbols vs 0** in the deployed binary,
corroborating that a redeploy resolves the mechanism behind the 17 parity
xfails. But zero end-to-end native-build compiles succeeded via any
bootstrap-representative invocation. Concrete prerequisite: fix
`certificate.spl`'s `std.cert.*` imports, then run the authoritative
`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap` gate as the
real test (it also produces the deployable artifact).

## 2026-07-17 follow-up (SDNVALUE lane): "fresh-vs-deployed divergence" NOT REPRODUCIBLE; a real, separate class/enum collision found and fixed anyway

Picked up the "New fresh-vs-deployed divergence" item directly above. b1a58671
("enum-variant ctor calls misrouted to colliding class via bare-module
fallback", the Wall-2 fix) was the prime suspect. Verdict: **b1a58671 is
innocent, and the reported divergence itself could not be reproduced.**

### The divergence does not reproduce

The task's own minimal repro — a tiny `.spl` doing
`use std.sdn.value.SdnValue` then `SdnValue.Int(42)`, run via
`src/compiler_rust/target/release/simple run` — prints `ok` (succeeds) on
**both** a from-scratch fresh build (`cargo build --release` +
`cargo build --profile bootstrap -p simple-driver`, current source) **and**
the deployed 2026-07-11 `bin/release/x86_64-unknown-linux-gnu/simple`. No
divergence exists for the faithful, task-specified repro.

A second, more elaborate repro (`use compiler.backend.backend_types.*` +
`use std.sdn.value.SdnValue`, calling `SdnValue.Int(42)` inside `fn main()`)
DOES fail — with the exact reported error text
(`unknown static method Int on class SdnValue; did you mean 'int'?`) — but it
fails **identically on the 07-11 deployed binary and the fresh build**. Since
this exact symptom already reproduces on a binary that predates b1a58671 by
days, b1a58671 cannot be its cause, and there is no seed commit between
07-11 and now to bisect for it (the failure isn't new). The bug doc's own
prior entry already flagged this specific claim as "untested risk, not a
cleared item" / "unverified" — that caution was warranted; the claim does not
hold up empirically.

### A real, pre-existing collision found via the elaborate repro (fixed anyway)

The elaborate repro's failure is a genuine, previously-undocumented defect —
a **different** collision site than Wall-2's `use_bare_module_fallback`
fix, on the SAME "same name used for both a class and an enum" defect class:

- Two `struct SdnValue:` declarations exist in `src/compiler`
  (`src/compiler/70.backend/backend_types.spl:124`,
  `src/compiler/80.driver/init.spl:280`), neither with an `Int` method, next
  to the real `pub enum SdnValue:` (`src/lib/common/sdn/value.spl:28`,
  variant `Int(i64)`). When both get loaded into the same interpreter run,
  the interpreter's `classes`/`enums` registries are global/flat (the
  already-documented "same struct name in 2 modules = runtime collision"
  landmine), and `interpreter/expr/literals.rs`'s `Expr::Identifier`
  handling checks `classes.contains_key(name)` **before** `enums`, so the
  bare identifier `SdnValue` resolves to `Value::Constructor` (the class)
  whenever both a class and an enum share the name — for ANY call made from
  inside a function/method body (module top-level bypasses this: a
  module-level `env` pre-registers a direct `Value::EnumType` binding, per
  the same mechanism Wall-2 documented).
- `SdnValue.Int(42)` then reaches `handle_constructor_methods`
  (`interpreter_method/special/objects.rs`), which only searched the class's
  own static methods and errored — it never considered that the method name
  might be a genuine enum variant on a same-named enum.

**Fix** (`src/compiler_rust/compiler/src/interpreter_method/special/objects.rs`):
`handle_constructor_methods` now falls back to enum-variant construction
(mirroring `interpreter_method/mod.rs`'s `Value::EnumType` construction arm)
when, and only when, the class has no matching static method AND a
same-named enum genuinely declares the requested method as a variant — real
static-method resolution is never shadowed (verified by a dedicated control
test).

**Regression tests** (`src/compiler_rust/compiler/src/interpreter_patterns.rs`,
`#[cfg(test)] mod tests`):
- `sdnvalue_style_enum_variant_survives_class_name_collision_on_constructor_call`
  — `struct SdnValue` (unrelated static method `empty`, no `Int`) + real
  `enum SdnValue: Int(i64)`, both loaded, constructed **inside a `fn` body**
  (required to reach the buggy path — see module-top-level note above).
  Before the fix: `evaluate: SemanticWithContext(... "unknown static method
  Int on class SdnValue" ...)`. After the fix: passes, payload extracted via
  match is `42`.
- `sdnvalue_style_real_static_method_still_wins_over_colliding_enum_variant_name`
  — control case: a real static method (`empty`) on the class must still be
  called normally, not shadowed by the new fallback. Passes both before and
  after (proves the fix doesn't touch the normal-resolution path).
- Both new tests were verified to actually exercise the fix (not
  false-positives): temporarily disabling the fix (`if false { ... }` swap,
  no `git stash` — this repo's concurrent-lane churn made `git stash`
  unreliable mid-session) reproduces the exact real-world error message on
  test 1 and leaves test 2 passing, confirming the tests have real
  discriminating power.

**Suite evidence:**
`cargo test -p simple-compiler --lib interpreter_patterns::` — 12/12 passed
(10 pre-existing incl. all 5 Wall-2 tests + 2 new), both before (10/10, new
tests not yet added) and after this change. Targeted
`interpreter_method::`/`interpreter_call::` runs: 8/8 and 4/4 passed
(includes the pre-existing `objects.rs` static-method-overload tests
immediately above the new fallback, confirming no interference). Full
`cargo test -p simple-compiler --lib`: 3040 passed, 256 failed, 1 ignored —
the 256-failure count matches this doc's own previously-recorded pre-existing
baseline exactly (GPU SIMD, VHDL codegen, `native_project` runtime-bundle
tests, etc., per the Wall-2 section above); no new failures attributable to
this change.

**Repro verification (final):** on a freshly rebuilt release binary
(`cargo build --release`, current source, debug instrumentation stripped
before this build) both `SdnValue.Int(42)` repros pass: the minimal one
already passed before this fix (never broken); the elaborate
`backend_types`-collision one, which failed identically on 07-11 and fresh
before this fix, now succeeds — its `unknown static method Int on class
SdnValue` symptom is resolved.

### Flagged, not investigated: a THIRD, separate collision (stale duplicate `std.sdn.value`)

While tracing the elaborate repro's remaining failure mode with temporary
`eprintln` instrumentation (added, verified, then fully stripped — no
instrumentation shipped), a **different**, still-open issue surfaced: even
with the class/enum-collision fix above in place, that specific repro
continued to fail — but for a wholly separate reason. Debug output showed
`handle_constructor_methods`'s enum lookup DID find an enum named
`"SdnValue"`, but with variants
`["Null", "bool", "i32", "f32", "text", "Array", "Dict", "Table"]` — this is
the shape of `src/compiler_rust/lib/std/src/sdn/value.spl` (a second,
differently-shaped `enum SdnValue:` bundled inside the Rust seed's own
`src/compiler_rust/lib/std/` tree), not the intended
`src/lib/common/sdn/value.spl` one (`Bool/Int/Float/String/...`). Something
in `compiler.backend.backend_types`'s transitive closure appears to pull in
the seed's private embedded copy of `std.sdn.value` and it wins (overwrites)
the global `enums` registry entry over the real one — an enum-vs-enum
shadowing bug, independent of the class-vs-enum mechanism fixed above. This
is almost certainly an artifact specific to that synthetic repro's plain
`run` + wildcard `compiler.backend.backend_types.*` import (the real
bootstrap path via `--source src/lib` would not pull in the seed's private
`src/compiler_rust/lib/std` copy) rather than something hit by real
bootstrap-representative invocations — **not chased further here**; flagged
as a possible follow-up if a stale/duplicate embedded `std` copy is ever
suspected of causing real (non-synthetic) failures.

### Files changed

- `src/compiler_rust/compiler/src/interpreter_method/special/objects.rs` —
  the fix (`handle_constructor_methods` enum-variant fallback).
- `src/compiler_rust/compiler/src/interpreter_patterns.rs` — 2 new
  regression tests appended to the existing `#[cfg(test)] mod tests`.

Not touched: `interpreter_method/mod.rs`'s `use_bare_module_fallback` /
`receiver_is_enum` (Wall-2, b1a58671) — confirmed innocent and left as-is;
its 5 regression tests remain green and unmodified.

## 2026-07-17 follow-up (CERT-IMPORTS lane): cert import wall FIXED

Fixed the concrete prerequisite noted above. Root cause: a single commit,
`97a9358145f8` ("test-infra: scaffold database + doc generation wiring
(debug required)", 2026-07-01), added both the real typed X.509 parser
(`src/lib/common/cert/pem.spl`, `src/lib/common/cert/x509_typed.spl`) **and**
`src/lib/nogc_sync_mut/tls/certificate.spl`/`validation.spl` in the same
change, but the latter two were scaffolded against an earlier-planned,
never-created API shape (`std.cert.x509`, `std.cert.chain`,
`std.cert.validation`) instead of the sibling `x509_typed.spl` module it
added alongside them — never reconciled. `cert/x509.spl`, `cert/chain.spl`,
`cert/validation.spl` never existed at any point in this repo's history
(confirmed via `git ls-tree` on the commit immediately before, at, and after
the unrelated "torn working copy" mass-delete/revert pair `e3e22d19da4`/
`369a3725bbe` that was initially suspected — ruled out, `cert/` only ever
held `pem.spl`+`x509_typed.spl`). The second, path-distinct
`src/std/nogc_sync_mut/tls/certificate.spl` flagged in the prior section is
confirmed still absent from `origin/main`/git entirely (on-disk only);
untouched, per instructions.

**Fix:**
- `certificate.spl`: repointed `std.cert.x509`'s
  `parse_certificate_der`/`parse_distinguished_name` and
  `std.cert.validation`'s `check_expiry` to the real `std.cert.x509_typed`
  API (`x509_parse_pem`, `X509Cert`, `x509_cert_cn`, `x509_cert_issuer_cn`,
  `X509Cert.not_before_unix`/`not_after_unix` + `rt_time_now()` for
  `is_valid()`). `TlsCertificate.parsed` changed type from `text` to
  `X509Cert`. Unused-but-still-cross-tier-re-exported helpers
  (`extract_cn`, `get_cert_subject_bytes`, `get_cert_issuer_bytes`,
  `decode_pem_block`) kept in place (documented why) since
  `gc_async_mut`/`nogc_async_mut` tier facades re-export them by name.
- `validation.spl`: same phantom-import defect
  (`std.cert.chain`/`std.cert.validation`), plus `verify_signature` — which,
  unlike the other three, has **no equivalent anywhere** in this codebase
  (real RSA/ECDSA X.509 signature verification was never implemented). Its
  only caller, `validate_chain`, had zero live callers and zero test
  coverage (confirmed via repo-wide grep), so it was deleted rather than
  stubbed, per the "implement or delete" rule. `gc_async_mut/tls/validation.spl`
  and `nogc_async_mut/tls/validation.spl`'s named re-export lists had
  `validate_chain` dropped in the same change (`gc_sync_mut`'s is a `.*`
  facade, unaffected). Tracked as a distinct, deliberately-deferred gap:
  `doc/08_tracking/bug/cert_chain_signature_verification_missing_2026-07-17.md`.

**Verification.** The real `--source src/lib` whole-tree collection run is
too slow to complete in-session (interpreted-seed entry-closure scan over
7,120 files; a from-scratch attempt was still mid-`gc_async_mut` after 9
minutes — see the pre-existing lexer/parse perf landmine in repo memory).
Instead verified with a minimal mirror `--source` root containing only the
five real files in the affected import closure (`base64.spl`, `pem.spl`,
`x509_typed.spl`, the fixed `certificate.spl`, the fixed `validation.spl`),
run through the same `native_build_worker.spl` phase-1 collector:
- **Before fix** (original file content): phase 1 failed immediately with
  exactly the three documented errors — `unresolved import 'std.cert.x509'`,
  `'std.cert.chain'`, `'std.cert.validation'` (all naming
  `certificate.spl` as the importer).
- **After fix**: zero `unresolved import 'std.cert...'` errors; phase 1
  passed and execution proceeded deep into real parsing/semantic analysis
  (observed parsing `base64.spl`'s actual statements, then into the
  self-hosting bootstrap's own `flat-bridge`/driver stage). It then hit
  `error: semantic: variable 'Map' not found` — a bare, file-less error
  message (matches the known "native-build eprint lost" landmine). Traced:
  `Map<K,V>` is a real stdlib type at
  `src/lib/nogc_sync_mut/src/map.spl`, deliberately excluded from the
  minimal mirror along with the rest of stdlib — this is a test-harness
  scope artifact (the compiler's own self-hosting driver code needs `Map`
  from the full stdlib), not a new defect from this fix. Repo-wide
  `grep -rn "std\.cert\.x509\b|std\.cert\.chain|std\.cert\.validation"` now
  matches only the explanatory comment in the fixed `validation.spl`.
- A full, unmodified `--source src/lib` run was started before the fix as a
  baseline (to independently confirm the pre-fix wall on the real tree, not
  just the mirror) but was killed once the mirror test gave equivalent
  proof faster; it never reached the `tls/` files in its alphabetical scan
  before being killed, so it contributes no additional evidence beyond the
  mirror test and the static grep sweep.

**Files changed:** `src/lib/nogc_sync_mut/tls/certificate.spl`,
`src/lib/nogc_sync_mut/tls/validation.spl`,
`src/lib/gc_async_mut/tls/validation.spl`,
`src/lib/nogc_async_mut/tls/validation.spl`.

**Next wall for the redeploy gate:** re-run the authoritative
`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap` gate (or a
full `--source src/lib` phase-1 collection to completion) now that the cert
wall is gone — not done in this lane, given the multi-hour interpreted-seed
runtime for a whole-tree pass observed above.

## 2026-07-17 follow-up (FULLBOOT lane): gate run — NOT-READY, hits the known Stage 2 LLVM symbol-lowering wall

Ran the gate per the section above, against the current working tree (not
a freshly-synced clean `origin/main` checkout — see the caveat in the
verdict below). No other lane had a live `--full-bootstrap` run for this
same objective (a stale-PID reference was already dead; a live
`--full-bootstrap` found via `pgrep` belonged to an unrelated lane in a
separate worktree, `build/worktrees/simpleos-sync-recover-gh`, with its own
`src/compiler_rust/target` — confirmed no shared state, so this run
proceeded in the main checkout).

**Command:**
```
CAP_MEM_MAX=32G scripts/resource/run_capped.shs timeout -k 30s 10800s \
  scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --mode=dynload \
  --full-cli --output=build/bootstrap --jobs=half
```
(No `--deploy` — this lane never touches `bin/`/`bin/release/`, per its
charter; deployment is user-gated.)

**Backend/profile resolution:** no script or Cargo-feature fix was needed.
LLVM 18 was detected on this host (`LLVM_FOUND=1`, `/usr/lib/llvm-18`), and
`bootstrap-from-scratch.sh` already conditions `--features llvm` on that
detection (line ~530) before invoking `cargo build --profile bootstrap -p
simple-driver`/`-p simple-native-all`. The "native backend 'llvm' is not
available" symptom described in this lane's charter only occurs when a seed
is hand-built without `--features llvm` (e.g. via the bare `cargo build
--profile bootstrap -p simple-driver` command in some manual recipes,
without the flag) — `--full-bootstrap` on a host with LLVM detected does
not hit that path. Confirmed empirically: the seed content-hash staleness
gate correctly detected the on-disk seed was stale (Rust source changed
since last build) and rebuilt both crates with `--features llvm`, 0 errors.

**Stage-by-stage outcome:**

| Stage | Result |
|---|---|
| Rust seed rebuild (`simple-driver` + `simple-native-all`, both `--features llvm`) | PASS — 0 errors, fresh seed at `src/compiler_rust/target/bootstrap/simple` (145MB, timestamped this run), carries this week's interpreter fixes (Wall-2 enum/class collision fix, SdnValue fix, cert-import repoint — all confirmed present via `git diff origin/main` on the 4 touched `tls/*.spl` files being empty) |
| Stage 2 (seed → `bootstrap_main.spl`, LLVM backend, `--entry-closure`) | **FAIL** — 19 files, 38 diagnostics, `llvm codegen: semantic: llvm global load referenced undeclared symbol <name>`. **This is a KNOWN, already-open, already-diagnosed wall** — `doc/08_tracking/bug/seed_llvm_mcall_direct_arg_count_mismatch_2026-07-14.md`'s "separate symbol-lowering bug" entry (documented before this run, same exact 19-file/38-diagnostic counts). An initial pass here misfiled this as a new regression; retracted after `git diff origin/main` showed the working tree still carries that investigation's uncommitted in-progress edits in exactly the affected codegen files. Full symbol table appended to the existing doc, not a new one. |
| Stage 3 (self-host verify) | Not reached — no Stage 2 binary to self-host from |
| Stage 4 (full CLI) | Refused seed fallback by design: `error: full CLI build requires a verified pure-Simple stage2/stage3 compiler; refusing seed fallback` (exit 2) — this is the gate's fail-closed behavior working as intended, not a separate defect |
| Stage 5 (MCP servers) | Not reached |

**Extended smoke checks / 3-of-17 parity-xfail spot-check:** NOT RUN — no
stage2/3/4 binary was produced this run, so there is no fresh
self-hosted candidate to check multi-fn `-c` compile / enum construct-match
/ Option-Result chains against, or to spot-run parity-xfail cases with. (A
smoke script was drafted for the next attempt:
`/tmp/claude-1000/-home-ormastes-dev-pub-simple/487db31f-7b5a-420a-8c9f-6d58fe0d2db7/scratchpad/fullboot_extended_smoke.sh`,
scratch-only, not part of the repo.)

**Verdict: NOT-READY.** The cert-import wall (previous blocker) is
confirmed fixed and the from-scratch seed rebuild is clean and carries all
of this week's interpreter-level fixes. But this run was **not a clean
origin/main run**: the working tree (71 uncommitted files across many
concurrent lanes at run time) still carries the
`seed_llvm_mcall_direct_arg_count_mismatch_2026-07-14.md` investigation's
uncommitted in-progress edits in exactly the codegen files that failed
(`llvm_lib_translate_expr.spl`, `backend_types.spl`,
`mir_lowering_stmts.spl`, plus the Rust-side
`native_project/{compiler,imports,mod,tests}.rs` +
`mir/lower/lowering_expr_builtin.rs`, all dirty vs `origin/main`). Stage 2
failed with **exactly** that doc's already-diagnosed 19-file/38-diagnostic
symbol-lowering wall — the fingerprint match is strong evidence this is the
same known bug, not a new defect, but it is an *inference from matching
counts*, not a direct verification against a clean tree. In particular,
this run's Stage 2 showed **zero** `mcall_direct` argument-count errors
(that doc's earlier, now-fixed 43-file wall), which means the seed carries
that fix — but whether that fix is committed on `origin/main` or only lives
in the dirty, uncommitted Rust sources this seed was built from was **not
checked**. If it turns out to be uncommitted, a coordinator re-running "this
same command" from a freshly-synced clean `main` could hit the earlier
43-file arg-count wall instead of this 19-file one, and "repair import-key
normalization" (that doc's prescribed next step) would not by itself be the
complete remaining work. Concrete asks for whoever picks this up: (1)
reconcile/commit the working tree to a known state (commits are the
coordinator's call, not this lane's), (2) then confirm which wall a truly
clean `origin/main` checkout hits before trusting "repair import-key
normalization" as the sole remaining prerequisite, (3) fix it, (4) re-run
this same gate command. Out of this gate-runner lane's scope to fix (a fix
lane should pick it up) — this lane's job was to run the gate and classify
the failure correctly, which required one self-correction: an earlier pass
in this same lane briefly misfiled this as a new regression, retracted once
cross-checked against `git log`/`git diff origin/main` (see the referenced
doc's 2026-07-17 follow-up for the full correction trail).

**Evidence paths:** `build/native_probe/redeploy-gate-fullboot-20260717.log.gz`
(gate wrapper log), `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage2-native-build.log.gz`
(19-file failure detail — also fully reproduced in
`doc/08_tracking/bug/seed_llvm_mcall_direct_arg_count_mismatch_2026-07-14.md`'s
2026-07-17 follow-up section so the gzip does not lose load-bearing
evidence), `build/bootstrap/logs/x86_64-unknown-linux-gnu/rust-seed-build.log`
and `rust-native-all-build.log` (clean seed rebuild evidence, both plain
text, small).
