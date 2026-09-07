# `simple ui` is dead: backend_loader.spl calls an undefined `_simple_binary()`

- **Filed:** 2026-09-06
- **Status:** FIXED (primary defect); the downstream residual is also FIXED 2026-09-06 (see § Residual and § Fix — residual)
- **Component:** `src/app/ui/backend_loader.spl`
- **Severity:** high — the whole product `ui` command never reaches any backend

## Symptom

`src/app/ui/backend_loader.spl` called `_simple_binary()` at three sites —
`run_ui_backend_dyn` (:41), `run_ui_cli_backend_dyn` (:53), `run_ui_render_dyn`
(:68) — but **no definition existed** in the file, anywhere in the repo, or in
git history: `git log -S'fn _simple_binary'` finds only `c4df31edf6b`, the
commit that added the CALL. The Rust driver dispatches `ui` to
`src/app/ui/cli_entry.spl` (`src/compiler_rust/driver/src/main.rs:481`), so
every `simple ui <mode> <file>` invocation hit it.

Reproduced 2026-09-06 with the bootstrap seed:

```
$ src/compiler_rust/target/bootstrap/simple run src/app/ui/cli_entry.spl ui tui \
      test/05_perf/ui_slim/t1_greeting.ui.sdn
[jit-fallback] unresolved external symbol '_simple_binary': whole module dropped to the interpreter (expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1 to turn this into a hard error.
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile: Module error: unresolved external symbol '_simple_binary' would NULL-jump in JIT; deferring to interpreter
error[E1002]: function `_simple_binary` not found
```

(Note the argv shape: `cli_entry.parse_ui_cli()` skips arguments until it sees
the literal `ui`, so a direct `run cli_entry.spl tui <file>` merely prints
usage. The `ui` token is required.)

## Fix

Defined `fn _simple_binary() -> text` in `src/app/ui/backend_loader.spl`,
resolving in the same order as the private
`src/app/ui/build.spl:229 _find_simple_binary()`:

1. `SIMPLE_BINARY` env var when set and non-empty,
2. `bin/simple.exe` / `bin/simple` when `file_exists` confirms it,
3. otherwise the bootstrap seed `src/compiler_rust/target/bootstrap/simple`.

`build.spl` is deliberately **not** imported — it drags the 875-file
`src/app/ui/main.spl` closure into the `simple ui` startup path, which the
`check-ui-slim-closure.shs` gate exists to prevent. The small order is repeated
instead, with a comment pointing at the original.

### Runtime-boundary record (spipe.md § file/process/env I/O)

- **runtime_need:** read `SIMPLE_BINARY`; probe candidate interpreter paths on disk.
- **facade_checked:** `std.nogc_sync_mut.io.env_ops.env_get` (already imported),
  `std.nogc_sync_mut.io.file_ops.file_exists` (newly imported; already inside the
  `cli_entry.spl` closure, so the closure gate does not grow).
- **chosen_path:** `reuse-facade`.
- **rejected_shortcuts:**
  - *"Use the running executable."* No current-executable facade exists. The
    nearest candidates — `std.io_runtime.get_args` / `app.io.cli_ops.cli_get_args`
    — return the **script** path at index 0 under `simple run foo.spl a b`
    (measured 2026-09-06: `count=4 / arg=[./_argv_probe.spl] / arg=[ui] / …`), so
    `argv[0]` would try to spawn a `.spl` file as a program. Marked
    `# ponytail:` in the source: prefer a real facade once one lands.
  - *Add a raw `rt_*` extern for the executable path.* Runtime-boundary change
    this lane does not own.
  - *Validate a candidate with a `--version` spawn* (as `build.spl` does). A dead
    binary still answers `--version` (`.claude/rules/vcs.md`, stage-binary guard),
    so it discriminates nothing and costs a process on every UI launch.

## Specs (both required by `.claude/rules/testing.md`)

`test/01_unit/app/ui/backend_loader_binary_spec.spl` — 5 examples:

- **Reproducing:** "resolves a real interpreter path for the spawned UI backend"
  and "honours an explicit SIMPLE_BINARY override" — both failed
  `semantic: function \`_simple_binary\` not found` before the fix.
- **Generalization:** "maps every known backend key to a backend entry script
  that exists" (all 10 keys incl. `tui_shared_wm`), "falls back to the TUI entry
  for an unknown backend key", "keeps the shared-WM backend distinct from the
  plain TUI backend" — these probe the loader's *other* child-process input,
  `_backend_entry_path`, which had no coverage either.

RED (pre-fix): `5 examples, 2 failures`. GREEN (post-fix): `5 examples, 0 failures`.
Run with `src/compiler_rust/target/bootstrap/simple run <spec>`.

## Verification

- `check-ui-slim-closure.shs src/app/ui/cli_entry.spl …` →
  `PASS — 118 file(s) in closure, 0 forbidden`.
- The `_simple_binary` / `E1002` failure is gone from the end-to-end
  `simple run src/app/ui/cli_entry.spl ui tui …` transcript.

## Residual (FIXED 2026-09-06 — separate defect, see § Fix — residual)

`check-ui-slim-startup.shs --binary src/compiler_rust/target/bootstrap/simple
--lane T1 --samples 3 --warmup 1` still fails, but now for a **different**
reason:

```
FAIL — 3 sample(s) attempted, T1, 3 invalid: run 1 produced no
'ui-slim-t1-greeting' in its transcript (rc=3, …)
transcript: build/ui_slim/startup/T1_20260906T045903Z_fail.txt
```

The transcript ends at `UI_SLIM_HARNESS_EOF_BEFORE_MARKER`. The backend entry
itself is healthy — run directly it paints the frame containing the marker:

```
$ … run src/app/ui/backend_entry_tui.spl --file test/05_perf/ui_slim/t1_greeting.ui.sdn --port 3000 --ui-access-db ""
┌─ UI Slim T1 ─┐
│ui-slim-t1-greeting│ …
```

**Root cause (unfixed):** `backend_loader` spawns the backend through
`std.nogc_sync_mut.io.process_ops.process_run`, which *captures* stdout into a
pipe and only replays it via `_print_child_output` after the child exits. A TUI
child therefore never gets the harness pty, and the alt-screen frame never
reaches the transcript. `process_ops` exposes no tty-inheriting exec
(`process_run`, `process_run_bounded`, `process_spawn_piped`, … are all
pipe-based), so fixing this needs either a new smallest-owner facade in
`process_ops` (exec/inherit-stdio) or an exec-replace in the loader — a
runtime-boundary decision outside this lane's owned files.

**Unblock condition:** an inherit-stdio (or exec-replace) process facade exists
and `backend_loader` uses it for interactive backends; then re-run the T1 lane.

## Fix — residual (2026-09-06)

The residual is closed without touching the runtime boundary: the `tui` backend
no longer spawns at all. `src/app/ui/cli_entry.spl` gained a single dispatch
point, `dispatch_ui_backend(backend, file_path, port, access_db_path)`, plus the
declarative seam it consults:

```
pub fn ui_backend_launch_mode(backend: text) -> text:
    if backend == "tui":
        return "in-process"
    "spawn"
```

`gui` / `desktop` / `auto` are resolved through `detect_gui_backend()` *before*
the seam is consulted, so a headless box that detects `tui` also runs
in-process. When the mode is `in-process` the dispatcher calls
`app.ui.tui.app.run_tui(file_path)` directly and the TUI inherits this process's
stdin and tty; every other backend — `tui_shared_wm` explicitly included, since
it drives a shared window manager over IPC rather than this terminal — still
goes through `run_ui_backend_dyn` unchanged. `backend_loader.spl` is untouched.

Why in-process rather than a new facade: the unblock condition above asked for
an inherit-stdio process facade, which is a runtime-boundary change this lane
does not own. Importing the TUI is free in closure terms — the TUI closure is
already compositor-free, and `check-ui-slim-closure.shs` still reports
`PASS — 149 file(s) in closure, 0 forbidden` (up from 118).

Evidence — the T1 startup lane, which is exactly what the residual blocked, is
now green:

```
$ sh scripts/check/check-ui-slim-startup.shs --binary src/compiler_rust/target/bootstrap/simple \
      --lane T1 --samples 3 --warmup 1
metric=launch_to_marker_and_exit clock=gdate_ns max_rss_bytes=271400960 min=6425.189ms max=7196.897ms spread=771.708ms
PASS — 3 sample(s), T1, median 6801.520 ms, p95 7196.897 ms, label=diagnostic
```

Regression spec: `test/01_unit/app/ui/ui_cli_tui_inprocess_spec.spl` (6/6). It
pins the seam and, because neither TUI route can be driven to completion under
the runner (the real route's watcher is synchronous on the seed lane and the
stub blocks on `input("")`), proves the routing with a spawn-poisoning oracle:
with `SIMPLE_BINARY=/bin/echo` and a missing `.ui.sdn`, `tui` must return 1
(`run_tui`'s file-not-found — no child ever ran) while `tui_shared_wm` and `web`
must return 0 (`/bin/echo` ran). The two codes are mutually exclusive, so a
revert to spawning flips the `tui` example.
