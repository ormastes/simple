# Stage-4 Redeploy: Failure Root-Cause & Two-Sided Fix Design

**2026-07-07 correction:** the original hypothesis in §2/§3.2/§4.1/§4.2 below
was refuted by a later worker. The seed parser's `parse_parameters`
(`src/compiler_rust/parser/src/parser_impl/core.rs`) **already** accepts
`mut <name>: <Type>` in parameter lists — there was no seed parser gap; the
observed failure was a *stale seed binary* being tested. The "duplicate
`target_presets.spl`" finding was also a misread: `src/compiler/backend` is a
git-tracked symlink (mode 120000) to `70.backend`, so there is only one real
file. The actual root cause was unbounded recursive-descent recursion in the
seed parser (no depth guard) → stack overflow → SIGABRT, triggered by the
parse error's recovery path, not by `mut` itself. That fix **landed**: origin
commit `4274c4f3f20b` (cherry-picked from change `9f1a7bd`) adds
`MAX_PARSE_RECURSION_DEPTH = 512` guards threaded through
`parse_expression`/`parse_type` in `expressions/core.rs`, `parser_types.rs`,
`parser_impl/core.rs`, `lib.rs`, plus regression tests in
`recovery_bound_tests.rs`. See the corrected §2/§3.1/§3.2/§4.1/§4.2 below.

**Status:** ACTIVE design (2026-07-07). Companion plan:
`doc/03_plan/cert/redeploy_selfhost_plan.md` (§ 2026-07-06/07 failure taxonomy).
**Goal:** unblock the stage-4 self-host rebuild that ~130 frozen source fixes
depend on, by fixing the last open failure class (silent SIGABRT) on BOTH the
Rust seed side and the pure-Simple source side, then bootstrap **pure-Simple
only** (reusing the fixed seed) in an isolated worktree.

---

## 1. Context and constraints

- **Pipeline:** Rust seed (`src/compiler_rust/target/bootstrap/simple`) →
  stage2 (`bootstrap_main.spl`) → stage3 (self-host replay) → stage4 (full CLI
  `src/app/cli/main.spl`) → gate → deploy to `bin/release/<triple>/simple`.
- Stage2/3 currently fail with the known empty-MIR-bodies bug
  (`doc/08_tracking/bug/bootstrap_stage2_empty_mir_bodies_2026-07-05.md`);
  stage4's **seed fallback** is therefore the operative path and is where the
  failure classes below were observed.
- Seed IR-level fixes (545× method-arity, 25× `rt_dir_create` extern-sig) are
  landed and verified absent from post-fix logs. The `export use *` rejection
  is a warning, **not** an error (verified at `module_system.rs:563` +
  passing unit test) — treat any plan that "fixes" it as a regression.
- Shared WC: parallel sessions force-push main and edit the working copy;
  therefore all fix work happens in a **git worktree** and lands via commit,
  never via long-lived uncommitted WC state.
- Resource sweeper kills `native_build_main` at RSS ≥ 24 GB → builds use
  `--threads 8` and are always instrumented (`echo RC=$?`).

## 2. The open failure (class 4): evidence chain

> **[CORRECTED 2026-07-07]** The "two defects" interpretation below is
> WRONG for defect 1: there is no seed parser gap for `mut` parameters (see
> top-of-file correction note). The real single root cause is defect 2
> (unbounded recursion in the parse-error path), independent of what
> specific token triggered the original parse error. The "duplicate module"
> secondary finding is also WRONG — `src/compiler/backend` is a symlink to
> `70.backend`, not a second copy.

Instrumented run 2026-07-06 11:58→14:08 (first run ever to capture an exit
code for this class):

```
[parser_error_ctx] path src/compiler/backend/target_presets.spl kind 167 text '->'
[parser_error] line 318:101: unexpected token in expression: ':'
[parser_error_ctx] path src/compiler/backend/target_presets.spl kind 161 text ':'
thread 'simple-main' (3614497) has overflowed its stack
fatal runtime error: stack overflow, aborting     → RC=134 (SIGABRT)
```

Failing source line (`target_presets.spl:318`):

```spl
fn preset_apply_compile_options(preset: TargetPreset, mut options: CompileOptions) -> CompileOptions:
```

Interpretation — **REFUTED, kept for incident-history record only:**

1. ~~**Seed parser gap — `mut` parameter modifier.** The seed does not accept
   `mut <name>: <Type>` in a parameter list.~~ **FALSE.** `parse_parameters`
   in `src/compiler_rust/parser/src/parser_impl/core.rs` already checks for
   and consumes a leading `TokenKind::Mut` before the param name (verified
   directly in the current tree). The `mut options: CompileOptions` in the
   failing line was never the problem; the parser was simply being exercised
   with a **stale seed binary** that predated (or otherwise lacked) this
   handling. The `-> CompileOptions:` tail surfacing as "unexpected token"
   was a downstream symptom of defect 2, not of a `mut`-parsing gap.
2. **Seed error-recovery non-termination — the ACTUAL sole root cause.**
   After a parse error (of any kind — not specifically `mut`-related),
   recursive-descent parsing (`parse_expression`/`parse_type` and their
   recovery paths) had no depth bound and could recurse until the
   `simple-main` thread's stack overflowed → `abort()`. This converted a
   diagnosable one-line error into two days of "silent" build deaths. **This
   is the only real defect**, and it is now fixed (see §3.1).

Blast radius: irrelevant — the `grep -rEl 'fn [a-z_]+\([^)]*\bmut [a-z_]+:'`
census below was collected under the false premise that `mut` params needed
a workaround. No workaround was needed; the census is kept only as a record
of what was (mis)investigated: `src/compiler/70.backend/target_presets.spl`,
`src/compiler/70.backend/backend/vhdl_codegen_helpers.spl`,
`src/compiler/60.mir_opt/mir_opt/pattern_dispatch.spl`,
`src/compiler/60.mir_opt/mir_opt/collection_opt_core.spl`,
`src/compiler/60.mir_opt/_OptimizationPasses/io_passes.spl`.

**Secondary finding — duplicate module: FALSE.** `src/compiler/backend` is a
git-tracked **symlink** (mode 120000, verified via `git ls-tree HEAD
src/compiler/backend` → `120000 blob ... src/compiler/backend` pointing to
`70.backend`) to `src/compiler/70.backend`. There is exactly one
`target_presets.spl` on disk (`src/compiler/70.backend/target_presets.spl`).
The "duplicate module in the build closure" was a misread of the error log,
which reports the symlinked path as if it were a separate file. No #41-class
hazard exists here; see §4.2 (no-op).

## 3. Fix design — Rust seed side (both changes required)

### 3.1 Bound error recovery (correctness of failure, non-negotiable)

**STATUS: DONE / LANDED — origin commit `4274c4f3f20b` (cherry-picked from
change `9f1a7bd4f043a1edb25767e27e6c2d45fa2590ba`), 2026-07-07.** This was the
only real fix required to unblock stage4; see the top-of-file correction
note.

- **Where (as landed):** `src/compiler_rust/parser/src/expressions/core.rs`,
  `src/compiler_rust/parser/src/parser_types.rs`,
  `src/compiler_rust/parser/src/parser_impl/core.rs` (defines
  `pub const MAX_PARSE_RECURSION_DEPTH: u32 = 512;`),
  `src/compiler_rust/parser/src/lib.rs`, plus regression tests in
  `src/compiler_rust/parser/src/recovery_bound_tests.rs`.
- **What (as landed):** a `parse_recursion_depth` counter threaded through
  `parse_expression` and `parse_type`; on exceeding `MAX_PARSE_RECURSION_DEPTH`
  (512), emit a located `parse error (recovery limit)`-style `Err` instead of
  recursing further. This directly prevents the stack overflow regardless of
  what triggered the original parse error (it was never specific to `mut`
  params).
- **Failure contract (as landed):** budget exhaustion returns a bounded,
  located `Err` up the driver instead of aborting. **Never** abort/overflow —
  verified by `recovery_bound_tests.rs`, which runs on a production-sized
  64MB stack and asserts a bounded `Err` + no abort.
- **Acceptance (met):** regression tests assert bounded `Err`, no SIGABRT,
  even for deliberately unparseable/deeply-nested input.

### 3.2 Accept `mut` parameter syntax — **N/A: was never broken**

**STATUS: N/A — no work needed.** `parse_parameters`
(`src/compiler_rust/parser/src/parser_impl/core.rs`, ~line 1043) already
accepted an optional leading `mut` token before a parameter name before any
of this investigation started (confirmed by direct inspection of
`self.check(&TokenKind::Mut)` in the current tree, and confirmed independently
in the landed commit's own message: "mut-parameter syntax is already accepted
by parse_parameters (verified), so no source rewrites are needed"). This
section is retained only to document that the originally-proposed work item
does not exist; do not schedule it.

## 4. Fix design — pure-Simple side

### 4.1 `mut`-param seed compatibility — **SKIPPED: unnecessary**

**STATUS: SKIPPED.** The premise (seed can't parse `mut` params, so `.spl`
sites must be mechanically rewritten to avoid the syntax) is false — see
§3.2. The seed already accepts `mut <name>: <Type>` in parameter lists, so
none of `target_presets.spl`, `vhdl_codegen_helpers.spl`,
`pattern_dispatch.spl`, `collection_opt_core.spl`, or `io_passes.spl` need
the `_in`-suffix rebind rewrite shown below. **Do not apply this rewrite —
it would be a needless, purely-cosmetic churn of working code.** The
mechanical rule is left here only as a historical record of the (abandoned)
plan:

```spl
# NOT APPLIED — kept for reference only, see status note above
# before
fn preset_apply_compile_options(preset: TargetPreset, mut options: CompileOptions) -> CompileOptions:
    options.gc_off = preset.no_gc
    ...
# after
fn preset_apply_compile_options(preset: TargetPreset, options_in: CompileOptions) -> CompileOptions:
    var options = options_in    # seed-compatible mut rebind
    options.gc_off = preset.no_gc
    ...
```

### 4.2 "Duplicate" `target_presets.spl` reconciliation — **NO-OP, no reconciliation needed**

**STATUS: NO-OP.** `src/compiler/backend` is a git-tracked symlink (mode
120000) to `src/compiler/70.backend` — verified with
`git ls-tree HEAD src/compiler/backend` (shows `120000 blob ...
src/compiler/backend` → target `70.backend`) and `readlink
src/compiler/backend`. There is only **one** real file on disk:
`src/compiler/70.backend/target_presets.spl`. `src/compiler/backend/target_presets.spl`
is the same inode reached through the symlink, not a second copy. **Do not
diff, "reconcile", or delete anything here** — the original steps 1-3 below
were based on a misread of the error log (which prints the symlinked path)
and would be destructive no-ops at best (deleting through the symlink
deletes the only copy) or actively harmful at worst. Left below only as a
record of the abandoned (incorrect) plan:

1. ~~`diff src/compiler/backend/target_presets.spl src/compiler/70.backend/target_presets.spl`.~~
2. ~~Find importers of each...~~
3. ~~Keep exactly one... delete the other.~~

## 5. Bootstrap flow (pure-Simple only) + verification

All in an isolated worktree (`git worktree`), committed before building:

```bash
scripts/bootstrap/bootstrap-from-scratch.sh          # NO --full-bootstrap: reuse fixed seed
# stage4 candidate lands under build/bootstrap/full/<triple>/simple (worktree-local)
sh scripts/check/cert/redeploy_gate/redeploy_gate.shs <candidate>   # 12 checks
```

Instrumentation contract (mandatory, from the class-4 lesson): wrap the build
in `sh -c '...; echo "RC=$? END $(date -Is)"'`, keep stderr, `--threads 8`,
record peak RSS if feasible. A run with no recorded RC is a process failure
regardless of build outcome.

Verification matrix (what "done" means):

| Check | Expected | Closes |
|---|---|---|
| stage4 RC | 0, binary exists | class 4 |
| parse errors in log | 0 (warnings allowed) | 3.2/4.1 |
| gate `GATE: N/M PASS` | all executed checks PASS | redeploy candidacy |
| `enum-payload` fixture | prints 42 | #109 regression guard |
| `class-in-array-mutation` (interpret mode) | prints 777 | #112 |
| `cfg-arch-dispatch-a/b` | self-check PASS | #45 |
| struct-copy-isolation | prints 5 | #91/#108 line |

Deploy (separate, gated on user go-ahead): backup
`bin/release/x86_64-unknown-linux-gnu/simple` → `.bak-<date>`; `cp` new to
`.new` then `mv` over (dodges "Text file busy"); rerun gate against the
DEPLOYED path; rollback = `mv` the backup back. `.mcp.json` launch-path copy
per `.claude/rules/code-style.md` § MCP servers.

## 6. Risks / notes

- **Seed rebuild required after 3.x** (`cargo build --profile bootstrap
  -p simple-driver --features llvm`, then `-p simple-native-all`): do not run
  while another cargo holds the target dir; check `pgrep -af 'cargo build'`.
- Native-cache staleness after seed changes is handled by #69's
  compiler-fingerprint fix; still prefer a fresh `--cache-dir` in the
  worktree for the proving run.
- Parallel sessions may land overlapping fixes (user reports another lane
  already passed seed+full bootstrap); before coding, `git fetch` + check
  whether error_recovery.rs / the mut-param sites changed upstream — if the
  fix already exists upstream, verify it instead of duplicating it.
- The 09:53 run died ~4 min in vs the instrumented run's 2h10m: recovery-loop
  runtime varies with thread contention; do not read run-length as progress.
