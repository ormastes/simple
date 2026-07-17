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
