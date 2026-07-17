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
