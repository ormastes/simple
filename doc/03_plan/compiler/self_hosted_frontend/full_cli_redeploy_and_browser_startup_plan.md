# Plan — Full-CLI Self-Host Redeploy + Browser `--open` Startup Recovery

**Date:** 2026-07-07
**Status:** OPEN — agent-executable
**Owns:** Task #21 (compiled-frontend + parser gap blocking full-CLI redeploy) and
Task #29 (`--open` startup regression). Also retires the `build lint` routing bug.
**Design pair:** `doc/05_design/compiler/parsing/frontend_parser_gaps_and_lazy_closure_design.md`
**Parser-gap mechanics:** `doc/03_plan/compiler/self_hosted_frontend/parser_completion.md`
(see the 2026-07-07 section appended there — this plan references it rather than duplicating).

---

## 0. Why one plan for two tasks

Task #21 and Task #29 share a single root: the self-hosted frontend still runs
**interpreted** on the `native-build → cli_run_file` lane (`~0.8 ms/char` linear
parse), so every module pulled into a build/startup closure multiplies wall time.
- Task #21 is the **structural** fix (run the frontend compiled + close the
  parser feature gap so a fresh full-CLI binary can be produced and deployed).
- Task #29 is the **short-term** fix (shrink the interpreted `--open` closure via
  `use lazy`, independent of #21) plus the statement that #29's workaround becomes
  **removable** once #21 lands.

Evidence base (all verified 2026-07-07 against the deployed binary):
- `doc/08_tracking/bug/bootstrap_stage4_graph_load_timeout_2026-07-05.md` — the
  interpreted-parse root cause, scaling curve, and the `mut`/destructuring parse
  divergence (§4 of that record).
- `doc/08_tracking/bug/browser_open_startup_regression_module_closure_2026-07-07.md`
  — 51s → >18min regression, "not a hang", module-closure driver.
- `doc/08_tracking/bug/deployed_binary_interp_extern_and_module_table_constraints_2026-07-07.md`
  — which parts go obsolete after redeploy (§Track C3 below).
- `doc/08_tracking/bug/build_lint_routes_to_rust_clippy_not_cli_run_lint_2026-07-06.md`
  — retirement tied to the same delegation lane.

---

## Track A — Parser feature-gap closure (correctness blocker, Task #21)

Close one feature at a time. For each: grammar/parser edit → self-hosted parse
acceptance → `spec` regression → interpreter parity. **Acceptance gate per feature:
`bin/simple check <currently-failing file>` emits zero `[parser_error]` lines** (the
warnings that follow are unrelated lint noise and do not fail the file).

### Status (2026-07-07)

- **A1 LANDED** — array-repeat expression `[value; count]` (count may be
  non-literal). New AST node `EXPR_ARRAY_REPEAT` / `ExprKind.ArrayRepeat(Expr,
  Expr)` (not desugared to a fill loop — kept as a first-class node so later HIR
  lowering can choose per-target codegen). `bin/simple check` is clean on
  `backend_metal.spl` and `window_scene_draw_ir.spl`. Regression:
  `test/unit/compiler/parser_gap_array_repeat_mut_param_spec.spl` (7/7).
- **A2 LANDED, peek-guarded** — `mut` parameters (`fn f(mut buf: [u8], ...)`).
  Opus review of the first patch proved a hardening gap: `mut` lexes as a plain
  identifier (kind 6), not a reserved word, so `fn f(mut: i32)` (a param literally
  named `mut`) parsed at base but was silently rejected by an unconditional
  text-match skip. Fixed in `parser_skip_mut_if_present`
  (`src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl`) with a
  one-token peek: save parser+lexer state (`parser_tok_save`/`lex_snapshot_save`,
  the same idiom `parser_stmts.spl`'s `me`-disambiguation and
  `parser_expr.spl`'s `try_skip_ident_generic_args` use), advance past `mut`,
  check whether the *following* token is itself a valid parameter-name token
  (identifier or `self`), then restore and only actually consume `mut` when that
  holds. Verified both directions: `fn f(mut: i32)` parses (base behavior
  restored) and `fn g(mut buf: [u8], ...)` still parses (patch's original goal).
  `bin/simple check` is clean on `backend_metal.spl`, `window_scene_draw_ir.spl`,
  and `pattern_dispatch.spl`.
- **A3 DEFERRED — corrected premise.** Originally scoped as "parser accepts
  destructuring `val`, add HIR let-lowering." The corrected finding: this is
  *not* parser-only — irrefutable destructuring `val PATTERN = EXPR` already
  parses fine today (interpreter path), and **still fails downstream** with HIR
  reporting "complex patterns not yet supported in let bindings." So even a
  parser-side fix would not unblock a native-build; the real gap is end-to-end
  pattern-let lowering, which needs (per the implementer's report):
  1. Extend the HIR let-binding lowering to accept irrefutable enum/struct/tuple
     patterns (not just plain identifiers), expanding `val PATTERN = EXPR` into a
     temp bind plus per-field/positional extraction statements.
  2. Thread the extracted bindings' types through the existing type-inference
     pass so downstream uses of the destructured names type-check.
  3. Handle nested patterns (tuple-of-struct, struct-of-enum) recursively rather
     than a single flat level, since real call sites (e.g.
     `src/std/nogc_sync_mut/env/variables.spl:358`) nest.
  4. Add interpreter-vs-self-hosted parity spec(s) asserting both `run` and
     `check`/`native-build` accept and lower the same construct identically
     (Track A's stated trap: divergence, not "parser is stricter").
  - **Reviewer's broader lowering-gap note (all future Track B items, not just
    A3):** the array-repeat node landed in A1 is presently **LOUD-unsupported**
    in the native-build HIR path (it moves the failure from parse-time to
    HIR-time — `native-build` still cannot compile a file using `[v; n]`, it just
    fails later and more clearly). Separately, a silent-`NilLit`-substitution
    gap exists only in the dead `compile_c_entry` stub (not on any live path),
    and `ArrayRepeat` is absent from the self-hosted `eval.spl` interpreter
    dispatch table entirely. None of these block A1's stated acceptance gate
    (`check` clean), but all three are concrete Track B follow-ups: HIR lowering
    for `ArrayRepeat`, removal/fix of the dead stub, and an `eval.spl` dispatch
    arm, tracked here so they are not lost.

Each gap is currently reproducible on the deployed binary (2026-07-07):

| Gap | Failing file (verified) | Parser error | Design section |
|-----|-------------------------|--------------|----------------|
| A1 array-repeat **expression** `[v; n]` | `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:257` (`[0u8; 12]`), `:265` (`[0u8; 28]`); `src/lib/common/ui/window_scene_draw_ir.spl:148` (`[0; z_span]`), `:232` (`[desktop_batch; windows.len()+2]`) | `expected ], got ; ';'` then `unexpected token in expression: ] ']'` | Design §2.1 |
| A2 `mut` parameters | `src/compiler/mir_opt/mir_opt/pattern_dispatch.spl:193` (`fn rewrite_block(..., mut stats: ...)`) — 74 repo files use it | `expected ), got Ident` | Design §2.2 |
| A3 destructuring `val` (irrefutable let) | `src/std/nogc_sync_mut/env/variables.spl:358` (`val Some(dollar_idx) = dollar_pos`) — 226 repo files | parse OK in interpreter, **HIR let-lowering** rejects (`complex patterns not yet supported in let bindings`); `parse_full_frontend` path rejects at parse | Design §2.3 |

### Ordering & dependencies
A1 (isolated, expression-parser only) → A2 (`Param` struct field + param parser +
call/lowering read-through) → A3 (parse accept + **HIR let-lowering**, the larger
change). A2 and A3 both gate a working full-CLI self-host (main.spl's 518-file
closure contains `mut`-param files), so both must land before Track C's redeploy.

### Work items
- **A1-1** Add `;`-repeat branch to the array-literal expression parser at
  `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl:503-513`, mirroring
  the sized-array **type** handling already present at
  `src/compiler/10.frontend/core/parser.spl:523-524` (parse `first_elem`, on `;`
  parse a count expr, emit a repeat array-lit AST — see Design §2.1 for the AST
  choice: lower to `expr_array_lit` with a repeat marker OR desugar to a fill loop).
  Acceptance: `check` clean on both `backend_metal.spl` and `window_scene_draw_ir.spl`.
- **A2-1** Add `is_mut: bool` to `struct Param`
  (`src/compiler/10.frontend/parser_types.spl:139`) and consume a leading `mut` in
  the param-position parser (Design §2.2). Acceptance: `check` clean on
  `pattern_dispatch.spl`; a focused spec asserts the flag round-trips.
- **A3-1** Accept irrefutable destructuring `val PATTERN = EXPR` at parse and add the
  HIR let-lowering that expands it to a temp bind + field/positional extraction
  (Design §2.3). Acceptance: `check` clean on `variables.spl`; interpreter-path
  parity spec (both `run` and `check` accept the same construct).
- **A-spec** For each of A1/A2/A3 add or extend a `_spec.spl` under the frontend
  spec tree (mirror an existing `parser_*` spec) so the gap cannot silently reopen.

### Risk
- A3 is the largest surface (touches HIR lowering, not just the parser) and has the
  highest regression risk on nested/tuple patterns. Land it last, behind its own spec.
- Interpreter vs self-hosted **divergence** is the trap: the fix is not "make the
  self-hosted parser reject less" but "make both accept the same grammar." Verify
  each feature with BOTH `simple run` and `simple check` (bug record §4).

---

## Track B — Compiled-frontend enablement (perf root fix, Task #21)

Goal: move `native-build`/`build`/`check` off the interpreted `cli_run_file` lane so
the frontend parser executes compiled. Target: `~0.8 ms/char → ~0.01 ms/char` class
(≈50–80×), turning the ~70–90 min full-CLI parse into ~1–2 min (bug record §5, item 1).

This is architectural and **cannot be proven without a rebuild**; it is a plan with
measurable milestones, not a spike.

### Work items (pick ONE of B-opt-a / B-opt-b after B-1 measurement)
- **B-1 (measure first)** With the existing default-off profiler
  (`SIMPLE_COMPILER_PHASE_PROFILE=1`, landed per bug record §5), capture the phase-2
  parse wall for a fixed medium closure (e.g. `src/app/context/main.spl`, 6 files) as
  the pre-change baseline. Milestone metric: phase-2 ms and ms/char.
- **B-opt-a** Register `native-build`/`build`/`check` as **compiled builtins** that
  call the linked-in compiled driver (`compiler_driver_run_compile`) directly instead
  of dispatching through `src/app/cli/dispatch.spl:99 cli_run_file(...)`. Hot path to
  bypass: `driver.spl:355` parse loop → `frontend.spl:34 parse_full_frontend` →
  `_FlatAstBridge/module_assembly.spl:455 parse_and_build_module` (bug record §1).
- **B-opt-b** Fix the interpreter JIT fallback so the parser hot path is JIT/AOT
  compiled (`run` currently logs `JIT compilation failed, falling back to
  interpreter`). Lower-certainty; only if B-opt-a is blocked.
- **B-2 (measure after)** Re-run B-1's fixed closure; **milestone acceptance: phase-2
  ms/char improves ≥20×** on the same closure. Record in the bug record.

### Dependency
Track B's end-to-end proof (a produced binary) depends on Track A being complete —
otherwise the fast build still fails at parse on `mut`/destructuring files (bug
record §5, item 4: raising `--timeout` alone is a non-fix).

### Risk
- The compiled driver's tagged-value ABI history (LLVM Stage-1 segfaults, per
  MEMORY.md) means B-opt-a must be validated on a small closure before the full set.
- Do NOT reintroduce the debunked "in-process backend for cross-target builds" hint
  as a fix — in-process shares the same interpreted parse (bug record §Status 2026-07-06).

---

## Track C — Redeploy + re-baseline procedure (Task #21)

Once Tracks A+B are green on a medium closure, produce and deploy a fresh full-CLI
binary, then re-baseline the platform-constraint facts.

### Work items
- **C1 Build** Run the full-CLI stage-4 build for the host triple (per
  `scripts/bootstrap/bootstrap-from-scratch.sh`; note `:430` passes no `--timeout` —
  set a generous one only as a safety net, not as the fix). Expected wall after Track
  B: single-digit minutes, not ~90.
- **C2 Deploy** Deploy `bin/release/<triple>/simple` (symlinked from `bin/simple`).
  Verify `bin/simple browser --help` **dispatches** (today it returns `error: file not
  found: browser` because the deployed binary predates the `browser` wiring — bug
  record §Status 2026-07-06). This is the concrete redeploy acceptance signal.
- **C3 Re-baseline the constraints record.** After redeploy, update
  `doc/08_tracking/bug/deployed_binary_interp_extern_and_module_table_constraints_2026-07-07.md`:
  - **Part (b) "module table baked at build time" — the specific stale entries go
    obsolete:** any `.spl` module added under `src/lib/**`/`src/app/**` *before* the
    C1 build is now resolvable (e.g. the `browser` subcommand wiring, and any sibling
    module deferred during #28 for table-invisibility reasons). The *general rule*
    (a new module added *after* the new build is still invisible until the next
    deploy) **remains true** — do not delete the record, mark which enumerated
    examples are now resolved.
  - **Part (a) "interpret-mode externs are a closed build-time table" — stays valid**
    in principle, but re-verify which externs the NEW binary registers (e.g.
    `rt_array_data_ptr`, `rt_write_u32s_to_raw`, `rt_u32s_from_raw`) with the same
    direct-probe method the record describes; update the "registered independently"
    examples to the new binary's actual table.
- **C4 Retire the build-lint routing bug.** With the compiled self-hosted binary
  deployed, retire the Rust-driver `lint` interception at
  `src/compiler_rust/driver/src/cli/commands/misc_commands.rs:126,181` (or make
  `handle_build` delegate `lint` to the self-hosted `cli_run_lint` lane) per
  `doc/08_tracking/bug/build_lint_routes_to_rust_clippy_not_cli_run_lint_2026-07-06.md`.
  Acceptance: `bin/simple build lint <file>` produces `cli_run_lint`-side output
  (e.g. `ui_backend_isolation_*` lines) and the ui-backend-isolation gate fires on
  the `build lint` lane, not only the pre-commit hook.

---

## Track D — Browser `--open` short-term fix (Task #29, independent of A/B/C)

The `--open` lane runs interpreted; the 51s → >18min regression came from
`src/app/ui.browser/app.spl` gaining host-WM/compositor imports whose transitive
closure is now parsed on every `--open` even though `--open` never calls into it.

**Empirical basis (verified 2026-07-07):**
- `init_host_wm` (and `HostWmConfig`/`HostBackendKind`/`Size`) are used **only** inside
  `run_shared_wm_browser` / `browser_shared_wm_config` (`app.spl:310-330`), reached
  **only** when `shared_wm == true` (`app.spl:333-337`). The default `--open` lane
  (`main.spl:88`, `shared_wm=false`) goes straight to `BrowserApp.new_*` / `app.run()`
  and never touches the compositor symbols.
- Simple **has** a `use lazy` import modifier that defers module load until first use
  (parser: `src/compiler/10.frontend/core/parser_decls_use.spl:163 decl_set_lazy`;
  interpreter: `src/compiler/10.frontend/core/interpreter/eval_decls.spl:87` →
  `register_deferred_module`, returns without loading). Smoke-tested 2026-07-07: a
  `use lazy` import whose symbol is unused does **not** load the module; first use
  resolves it correctly. This is the sanctioned mechanism — no numbered module split
  needed.

### Fix (D1, primary — lazy import)
Change the two host-WM imports in `src/app/ui.browser/app.spl:17-18` from `use` to
`use lazy`:
- `use lazy common.window_protocol.geometry.{Size}`
- `use lazy os.compositor.host_compositor_entry.{HostBackendKind, HostWmConfig, HostWmHandle, init_host_wm}`

Both symbol sets are referenced only inside the `shared_wm` functions, so the
compositor closure is deferred off the `--open` path entirely. `std.diag.{dbg_stage}`
stays eager (used on the hot path). In `src/app/ui.browser/main.spl:26`, evaluate
whether `HostBackendKind` (used only as the return type of the uncalled
`shared_wm_backend_kind_browser`, `main.spl:203`) can also be `use lazy`; type
annotations are runtime-erased in interpret mode, so this is expected safe — verify
per the D2 protocol.

### Fallback (D1-alt — structural split, only if lazy proves unsafe on this closure)
If a symbol turns out to force eager resolution, move `browser_shared_wm_config` +
`run_shared_wm_browser` into an existing `os.compositor` module (e.g. alongside
`host_compositor_entry.spl`) behind a single exported function, and have `main.spl`
call that entrypoint only on the `shared_wm` branch — so `app.spl` no longer imports
the compositor closure at all. **No `X2`/`_v2`/numbered module** (MEMORY.md directive);
merge into the existing compositor module.

### Measurement protocol (D2 — attribute the closure cost before/after)
`dbg_stage("browser", ...)` markers already bracket the startup path
(`app.spl:114,120,129,135,182,185,187,322,328,334,341,351`). Env-gate: `SIMPLE_DIAG=stage`.
- **Before:** run the target command, record wall to `launch_start` → `parse_start`
  (the module-load/closure phase) vs `parse_start` → `first_frame_done`. The
  regression is expected to sit in the pre-`parse_start` module-load closure.
- **After D1:** same markers; the pre-`parse_start` closure phase should collapse
  because the compositor modules are no longer loaded on the `--open` lane.
- Target command (from the bug record):
  `SIMPLE_GUI=1 SIMPLE_EXECUTION_MODE=interpret SIMPLE_LIB=src bin/simple src/app/ui.browser/main.spl examples/06_io/ui/hello_web.ui.sdn --open --backend=metal`

### Acceptance (D)
- `--open` reaches a visible window in **≤90s** on the `metal` backend (bug record
  targets ~51s parity; ≤90s is the ratchet gate).
- Browser specs stay green (run the `ui.browser` / `shared_wm_entrypoints` specs).
- **WM-hosted lane unaffected:** `--shared-wm` (or `SIMPLE_UI_BROWSER_SHARED_WM=1`)
  still joins the shared host WM — the lazy import must resolve on first use of
  `init_host_wm`, verified by an actual `--shared-wm --open` run reaching
  `shared_wm_init_done`.

---

## When Track D becomes removable

Track D is a closure-size mitigation on the **interpreted** startup path. Once Track
B lands (frontend runs compiled) and Track C redeploys, the `~0.8 ms/char` multiplier
is gone, so closure-size growth stops being startup-latency-critical and the `use
lazy` markers in `app.spl` are no longer load-bearing for latency. At that point:
- Keep `use lazy` only if it still expresses intent cheaply; otherwise revert to plain
  `use` in the same change that verifies compiled-startup latency is flat w.r.t. the
  compositor closure.
- Update this plan and the Task #29 bug record to CLOSED with the compiled-startup
  measurement as evidence.

---

## Cross-track dependency summary

```
A1 → A2 → A3  ──┐
                ├─→ C1 build → C2 deploy → C3 re-baseline → C4 retire build-lint
B-1 → B-opt → B-2 ┘
D1 → D2 (independent; ships now; removable after B+C)
```
