# CLI app child-process hang (browser_cli_log_modes / cli_log_modes TIMEOUT class)

**Filed:** 2026-11-12, from phase-2 triage on release/1.0.0 (Windows host).
**Severity:** P1 — hangs any spec that spawns the `cli` app; both log-modes specs
TIMEOUT at the runner's 360s hard cap.
**Owner lane:** cli / dispatch.

## Symptom

Specs that invoke the `cli` application as a child process hang indefinitely;
the phase-2 runner records TIMEOUT after the hard kill:

- `test/02_integration/app/browser_cli_log_modes_spec.spl` — TIMEOUT (every run)
- `test/02_integration/app/cli_log_modes_spec.spl` — hang on its first example

The hang reproduces **with a clean environment** (no `SIMPLE_*` vars), so it is
independent of the test-runner env-leak fixed in PR #8640.

## Evidence

- The phase-2 runner hardening (file-redirected stdout, stdin from `/dev/null`,
  `timeout -k 10 360`) kills the child at the budget — the grandchild holds no
  pipe after the fix, yet the `cli` invocation still never completes, i.e. the
  process is alive and blocked (not output-starved). Earlier diagnosis observed
  the child holding the stdout pipe open forever; after the pipe fix the child
  still never exits.
- Agent-19's log-modes sweep (PR #8551) independently recorded: "`cli` app
  broken even with clean env".
- Adjacent log-modes apps (context, info, install, list, os, record, search)
  fail only on stderr-purity/oracle drift; `cli` is the sole hanger in the
  family, pointing at dispatch/entry shutdown rather than a harness issue.

## Suspects

- `src/app/cli/**` entry/dispatch path never reaching process exit (event loop /
  pending handle) on Windows UCRT.
- The `cli` startup route's app-server handshake (browser_cli variant) blocking
  on a connection that never arrives.

## Repro

```
bin/simple.exe test test/02_integration/app/browser_cli_log_modes_spec.spl --timeout 300
# or directly: spawn `bin/simple.exe cli --version`-class child from a spec and wait
```

## Notes

- Not a test-harness defect: the same harness passes for every other
  log-modes app once the env leak is scrubbed.
- Not the seed banner: the banner prints to stderr and exits 0 elsewhere.

## 2026-11-13 — Root cause found (release/1.0.0, Windows host, lldb + seed trace)

Reproduced with the committed seed (`bin/simple.exe`, tree-matching bootstrap
seed) running `src/app/cli/main.spl` directly. The child is NOT blocked on an
event loop or a socket: it dies on cross-module name collisions, and the
failure is silent at the runner level for three compounding reasons.

### 1. Deterministic semantic abort: duplicate `GuiEvent` (product bug, fixed)

`bin/simple.exe run src/app/cli/main.spl --help` loads the whole flattened
cli graph (~98k items), then aborts (~140 s in) with:

```
error: semantic: ambiguous type `GuiEvent`: defined in
  src/lib/editor/00.common/gui_types.spl,
  src/lib/nogc_sync_mut/ui/gui_renderer.spl
  and none of them is imported by <entry>; import one explicitly
```

Two DIFFERENT types share the bare name `GuiEvent` in the co-compiled graph:
the editor record (`struct GuiEvent { kind, data }`, canonical shared record
per doc/08_tracking/bug/editor_gui_shared_record_owners_2026-10-04.md) and
the UI renderer event class (`class GuiEvent { native_id, kind, scancode, ... }`).
The cli entry co-imports both (browser dispatch -> app.ui.browser.app ->
gui_renderer; ide dispatch -> app.editor.gui_shell -> gui_types). The seed's
flattened-module type registry resolves bare names globally
(`module_cache.rs:2024 resolve_class_in_scope`): 2+ owned definitions with no
surviving binding = hard error. An explicit import at the use site does NOT
help (verified: `gui_shell_render.spl` import fix did not clear the error);
only unique names satisfy the flattened registry.

Fix: renamed the renderer class to `GuiWindowEvent`
(`src/lib/nogc_sync_mut/ui/gui_renderer.spl` + its 6 consumers); also added
the missing explicit `GuiEvent` import at the bare use site
`src/app/editor/gui_shell_render.spl:7`. After this, the browser app
(`src/app/browser/main.spl --help`) JIT-compiles and exits 0 with correct
output in ~25 s. The same collision blocked `browser_cli_log_modes_spec`.

### 2. JIT lane then fails one collision at a time (pre-existing tree debt)

With `GuiEvent` fixed, the JIT lane advanced and failed on the next
cross-module duplicate, one per compile:

- `file_modified_time` — `nogc_sync_mut/io/file_ops.spl` vs
  `nogc_sync_mut/sffi/io.spl` (fixed: sffi alias renamed
  `file_modified_time_raw`; no importer used the sffi copy).
- `int_to_str` — `compiler/10.frontend/core/types.spl` vs two identical
  copies in `compiler/35.semantics/lint/{stub_impl,wide_public}.spl`
  (fixed: lint copies renamed `lint_int_to_str`).
- next: `env_get` (7 definitions), and ~158 names tree-wide carry
  `co-compiled definitions` warnings. This is a pre-existing, tree-wide
  duplicate-symbol debt surfaced by the seed's HIR-lowering ambiguity check;
  whack-a-mole fixing is tracked separately from this P1.

### 3. Interpreter fallback ran the WRONG `main` (product bug, fixed)

On JIT failure the seed falls back to the tree-walk interpreter
(`exec_core.rs run_file_interpreted_with_args`). Evidence (lldb thread
stacks + `SIMPLE_TRY_PROBE=1`): the fallback loads all ~98k items, stamps
`engine=interpreter`, then exits 0 with NO output and never executes the cli
command. Cause: the cli entry (`src/app/cli/main.spl`) defined `main` only
via `export use app.cli._CliMain.main_and_help.*`; the flattened graph also
contains `fn main` from `app.ide.main` and `app.play.main` (both imported
for their CLI handlers), and interpreter `main` binding is
first-registration-wins in flattened item order — an imported module's
`main` won, so the "cli app" ran the ide/play entry with cli argv and
returned 0 silently. (Probe-verified: an entry file that defines its own
`main` always wins.) `reject_silent_no_op_module` cannot catch this because
the module does contain a `main` and executable statements.

Fix: `src/app/cli/main.spl` now defines `fn main` directly
(forwarding to `cli_main_with_execution_mode(false)`);
`main_and_help.spl` exports that owner and no longer defines `main`.

### 4. Runner-level TIMEOUT shape (seed runtime, diagnosed not rebuilt)

lldb on the blocked spec process (browser_cli run, 0 % CPU, 7 threads):
thread parked in `interpreter_extern::system::process_run_output_bounded`
wait loop (`system.rs finish_child_output_bounded`); reader threads blocked
in `ChildPipe::read` on the grandchild's inherited pipe. On Windows the
timeout kill (`child.kill()`, `system.rs:181`) terminates only the direct
child (cmd.exe); the grandchild `simple.exe` keeps the pipe write end, so
the bounded readers never see EOF and the spec's `process_run_bounded` wait
outlives its 120 s example budget by minutes. Combined with (1)-(3) — every
cli-app spawn burned its full budget or died silently — the spec never
reached a verdict inside the runner's 360 s cap. Root of THAT is the
collision chain above; the Windows grandchild-pipe retention is a separate
seed-runtime hardening item (compare
doc/08_tracking/bug/rust_async_process_unread_pipe_hang_2026-07-17.md).

### Verification snapshot (this fix, seed binary, Windows host)

- `bin/simple.exe run src/app/browser/main.spl --help`: exit 0, full help
  output, ~25 s (was: deterministic `GuiEvent` semantic abort).
- `bin/simple.exe test test/02_integration/app/context_log_modes_spec.spl
  --timeout 300`: 4 examples, 0 failures, verdict OK (no regression).
- `bin/simple.exe test test/02_integration/app/cli_log_modes_spec.spl
  --timeout 1500`: VERDICT REACHED (was: runner TIMEOUT at 360 s) — 7
  examples executed, 1 passed, 6 failed, outcome=ERROR. Failure breakdown:
  4 examples see empty child output because the seed's ~124 s JIT-compile of
  the cli graph exceeds the spec fixture's 120 s per-spawn budget; 2 examples
  fail on a pre-existing spec bug (`_run_cli_with_echo_delegate` is called at
  lines 83/91 but never defined in the spec).
- `browser_cli_log_modes_spec`: the early option-parsing examples pass; the
  URL-render example spins the real 4K render engine for 700+ s under the
  seed (the spec header itself documents render paths as too slow for the
  seed; the self-hosted binary is the intended runtime). Its verdict line is
  additionally vulnerable to the grandchild-pipe retention in (4).
- Remaining seed-side work (diagnosed here, not rebuilt per bootstrap policy):
  the `env_get` collision chain (~158 duplicate names carry
  `co-compiled definitions` warnings), the fallback-lane exit(1) landmine
  behind the entry-main fix, and the `finish_child_output_bounded`
  grandchild-pipe retention.
