# M5 arena-provenance defect class: no existing SFFI crossing to instrument

**Date:** 2026-08-05
Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
fixed" below).
**Severity:** Low-to-informational for now. This is a scoping gap, not an
observed memory-safety hole: no live code path was found where the hazard
the design doc describes can currently fire.

## Claim vs reality

`doc/05_design/compiler/interpreter/m5_strict_interpreter_mode_design.md` §4
("Provenance across the SFFI boundary") states two AST representations exist
and "only one has a gap":

1. `interpreter_extern/ast_sffi.rs` (Rust `simple_parser::ast::Expr`, exposed
   to Simple macros via thread-local `HashMap<i64, Expr>` registries and a
   monotonic, never-reused `AtomicI64` handle counter) — the design doc
   itself already concludes "**Already provenance-safe; nothing to add.**"
2. `_AstExpr/nodes.spl` (self-hosted compiler's parallel-array arena) — *does*
   recycle slot indices via a free-list, and its diagnosis-only
   `ast_gen_slot`/`ast_generation_bump()`/`ast_gen_check_index()`
   (`nodes.spl:109,369,384`) already exists but is gated
   `SIMPLE_AST_GEN_CHECK=1`/`SIMPLE_BOOTSTRAP_STAGE4=1`, not the strict-mode
   read gate.

The design doc's own remaining action item: "M5's addition: when a
`nodes.spl`-minted index crosses into an `interpreter_extern` SFFI call,
thread it as an `(idx, gen)` pair (M2's `NodeRef` shape) so a stale index
fails at the boundary, named, before Rust-side logic touches it — a thin
adapter over M2's mechanism, not new machinery."

An earlier addendum to `doc/03_plan/compiler/bootstrap/m_lane_status_2026-08-02.md`
(2026-08-05, poison-on-free pass) already flagged this item as "Not attempted
this pass; scoped as a separate, larger change (touches the SFFI call-site
shape, not just `value.rs`/`block_exec.rs`)" without further detail. This doc
supplies that detail.

## Measured 2026-08-05

Grepped for any point where a `nodes.spl`-minted `i64` arena index is passed
as an argument into an `interpreter_extern` SFFI function:

- `interpreter_extern/*.rs` (all ~60 files, including `ast_sffi.rs`): zero
  hits for `nodes.spl`, `expr_owner`, `arena_idx`, or any comment/identifier
  referencing the flat-array arena.
- `_AstExpr/nodes.spl` and `_AstExpr/accessors.spl`: the only `extern fn`
  declarations are `rt_env_get`/`rt_env_set`/`rt_env_remove` (used for the
  bootstrap-mode env mirror, `nodes.spl:112-114`) — no extern declaration
  anywhere in that module accepts or forwards an arena index to Rust.
- `ast_sffi.rs`'s handles (`register_expr`/`register_node`/... via
  `NEXT_HANDLE: AtomicI64`) are minted **independently** of `nodes.spl`'s
  arena; nothing in the registry-population call sites derives a handle from
  a `nodes.spl` slot index, and nothing in `nodes.spl` ever calls
  `register_expr`/`rt_ast_expr_*`.
- The one file whose name suggested a bridge —
  `10.frontend/_FlatAstBridge/convert_nodes.spl` — converts the flat arena
  into the pure-Simple `ParserModule`/HIR-facing shape (a **third**,
  in-language representation, entirely separate from `ast_sffi.rs`'s
  Rust-native registries). It calls no `interpreter_extern` SFFI function
  either.

**Conclusion: the crossing point the design doc's §4 describes does not exist
in the current codebase.** `nodes.spl` indices and `ast_sffi.rs` handles are
two index spaces that never meet. This matches the design doc's own framing
("Two AST representations; only one has a gap") more literally than the
follow-up sentence implies: there isn't yet a real call site where the gapped
representation's index reaches the SFFI boundary at all.

## Why this is filed, not fixed

Per this task's own scoping instruction: implement only when it fits a
"scoped implementation"; if a defect class needs something structural/
high-risk beyond that, file a bug instead of forcing it. Two options were
considered and both fail that bar:

1. **Instrument a real crossing.** None exists to instrument — there is no
   call site to add the `(idx, gen)` pair to without first inventing a
   feature (a new bridge from `nodes.spl` into `ast_sffi.rs`) that isn't part
   of this task and would itself need its own design review.
2. **Add a synthetic crossing purely to host the check.** Rejected: a
   fixture built around a crossing that doesn't occur in production code
   would not satisfy the plan's own exit bar ("a fixture that passes normally
   and traps under strict mode" describing a *real* defect shape, per the
   discipline the uninit-read and poison-on-free classes both followed) — it
   would prove the check code compiles, not that it catches anything a real
   caller could trigger. That is exactly the kind of vacuous-fixture failure
   this campaign's own memory notes elsewhere warn about.

## Recommended next step

Before this defect class can be implemented for real, someone needs to
either (a) find or introduce the actual call path by which a `nodes.spl`
arena index is meant to reach `interpreter_extern` today (e.g. is this
intended for a future self-hosted macro system that reads the flat arena
through Rust SFFI, not yet built?), or (b) narrow the design doc's §4 item to
state explicitly that it is forward-looking/speculative pending that bridge,
not a currently-exploitable gap. Either resolution is a design-level call,
not an implementation one — out of scope for this pass.

**Blocked on bootstrap?** No — this was pure investigation (grep across
`src/compiler_rust/compiler/src/interpreter_extern/*.rs` and
`src/compiler/10.frontend/**`), no build attempted.

## Re-verification 2026-08-09

Status confirmed **ARCHITECTURAL-OPEN**, and the finding still holds. Re-ran
the doc's own grep methodology in this worktree:

- `/usr/bin/grep -rn "nodes.spl\|arena_idx\|expr_owner" src/compiler_rust/compiler/src/interpreter_extern/*.rs` → 0 hits (same as originally reported).
- `_AstExpr/nodes.spl` and `_AstExpr/accessors.spl` still declare no `extern
  fn` that accepts/forwards an arena index to Rust — the only `extern fn`s
  present are the `rt_env_get`/`rt_env_set`/`rt_env_remove` bootstrap-mode
  mirror, unrelated to this crossing.

The conclusion is unchanged: there is no live call site where a `nodes.spl`
arena index crosses into `interpreter_extern` today, so there is nothing to
instrument without first inventing an unbuilt bridge feature — which is a
design decision, not an implementation task, and stays out of scope here. No
code changed; doc left OPEN.
