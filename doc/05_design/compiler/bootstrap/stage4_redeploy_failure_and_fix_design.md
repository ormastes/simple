# Stage-4 Redeploy: Failure Root-Cause & Two-Sided Fix Design

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

Interpretation (two defects, one incident):

1. **Seed parser gap — `mut` parameter modifier.** The seed does not accept
   `mut <name>: <Type>` in a parameter list. It misparses from the `mut`
   token onward, so the `-> CompileOptions:` tail (col ~101) surfaces as
   "unexpected token in expression".
2. **Seed error-recovery non-termination.** After the parse error, recovery
   (`src/compiler_rust/parser/src/error_recovery.rs`; note line ~302 already
   special-cases a `mut` lexeme) recurses/loops without a depth bound until
   the `simple-main` thread's stack overflows → `abort()`. This converted a
   diagnosable one-line error into two days of "silent" build deaths.

Blast radius of defect 1: `grep -rEl 'fn [a-z_]+\([^)]*\bmut [a-z_]+:'`
finds ≥5 compiler files — `src/compiler/70.backend/target_presets.spl`,
`src/compiler/70.backend/backend/vhdl_codegen_helpers.spl`,
`src/compiler/60.mir_opt/mir_opt/pattern_dispatch.spl`,
`src/compiler/60.mir_opt/mir_opt/collection_opt_core.spl`,
`src/compiler/60.mir_opt/_OptimizationPasses/io_passes.spl` — so a one-file
workaround cannot clear stage4.

**Secondary finding — duplicate module:** the error path names
`src/compiler/backend/target_presets.spl` while the numbered layout has
`src/compiler/70.backend/target_presets.spl`. Two same-name modules in the
build closure reproduce the #41 duplicate-struct field-resolution hazard and
must be reconciled (keep the `70.backend` one unless imports prove otherwise).

## 3. Fix design — Rust seed side (both changes required)

### 3.1 Bound error recovery (correctness of failure, non-negotiable)

- **Where:** `src/compiler_rust/parser/src/error_recovery.rs` (+ its callers
  in stmt/expr parsing).
- **What:** introduce a recovery budget: (a) a recursion-depth counter (or
  explicit fuel, e.g. 500 recovery attempts per file) threaded through the
  recovery path, and (b) a **must-advance invariant** — every recovery
  iteration either consumes ≥1 token or reduces nesting depth; if neither,
  bail out of the file with a fatal-but-graceful parse error.
- **Failure contract:** on budget exhaustion emit
  `parse error (recovery limit) at <file>:<line>:<col>` and return an `Err`
  up the driver, terminating the build with a nonzero exit and the file list
  of failed modules. **Never** abort/overflow.
- **Acceptance:** feeding current `target_presets.spl` to the *unfixed-3.2*
  seed parser must produce a bounded, located error (regression test with a
  deliberately unparseable file containing `mut` params + deep nesting);
  process exits cleanly, no SIGABRT.

### 3.2 Accept `mut` parameter syntax (feature parity, cheap-if-true)

- **Where:** seed parameter-list parsing (parser stmt/fn-signature path; the
  interner already interns `mut`).
- **What:** allow optional `mut` before a param name; represent it as the
  param's mutability flag if the seed AST has one, else **parse-and-ignore**
  (treat as annotation) — the seed only needs to *compile* the self-hosted
  compiler, whose semantics enforce mutability itself.
- **Guard:** if this turns out non-cheap (>~50 LOC or touches type checking),
  SKIP it and rely on the pure-Simple rewrite (§4) — 3.1 alone already
  converts the wall into a readable error list.
- **Acceptance:** seed parses `fn f(a: T, mut b: U) -> U:` and the stage4
  parse of all 5 affected files reports zero errors.

## 4. Fix design — pure-Simple side

### 4.1 `mut`-param seed compatibility (only if 3.2 is skipped)

Mechanical, semantics-preserving rewrite per site:

```spl
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

Rule: rename the param (`_in` suffix), first statement `var <name> = <name>_in`,
body otherwise untouched. Apply to every match of the census grep (re-run the
grep in the worktree; do not trust the cached list of 5). Per repo policy this
is recorded as a temporary seed-compat measure, NOT a language retreat —
`mut` params remain valid Simple; if 3.2 lands, these rewrites may stay (they
are harmless) but no new ones are required.

### 4.2 Duplicate `target_presets.spl` reconciliation

1. `diff src/compiler/backend/target_presets.spl src/compiler/70.backend/target_presets.spl`.
2. Find importers of each (`grep -rn "backend.target_presets\|70.backend.target_presets\|compiler.backend.target_presets" src/`).
3. Keep exactly one (expected: the numbered `70.backend` copy), update
   imports, delete the other. If they diverged, merge newest-truth per hunk
   before deleting. This also removes the #41-class duplicate-struct hazard.

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
