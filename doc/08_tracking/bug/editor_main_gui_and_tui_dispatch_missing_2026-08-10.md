# editor entrypoint never dispatches `--gui` or the TUI shell (2026-08-10)

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).
Found by: stream K4, anchoring hollow "comment-cheat" spec needles
(`doc/08_tracking/test/comment_cheat_spec_census_2026-08-09.md`)

## Symptom

`src/app/editor/main.spl` is the editor entrypoint. It advertises a `--gui`
option in `print_help()` (main.spl:76) but there is **no dispatch arm for it**.
Only `--gui-sdl` is wired:

```
src/app/editor/main.spl:48-51
    if args.contains("--gui-sdl"):
        val session = _editor_session_for(args)
        gui_shell_run_sdl(session)
        return 0
```

`--gui` therefore falls through to the readiness path and prints
`Ready for gui editor startup with N file(s).` — no window, exit 0.

Likewise, `editor_tui_run(session)` is never called from the entrypoint. It
exists (`src/app/editor/tui_shell.spl:31`) and has exactly one caller,
`src/app/editor/tui_main.spl:25`, which `main.spl` does not reach.

## Why it went unnoticed

Three spec assertions claimed main.spl wires both launchers:

- `test/03_system/gui/editor_gui_spec.spl` — `gui_shell_run(session)` and
  `editor_tui_run(session)`
- `test/03_system/gui/editor_buffer_spec.spl` — `editor_tui_run(session)`

All three were satisfied by main.spl:6-7, a header comment that describes the
two calls as "the intended dispatch hooks":

```
src/app/editor/main.spl:4-7
# Interactive launchers keep the heavyweight shell loops out of the readiness
# path; the legacy GUI contract still tracks the intended dispatch hooks:
# gui_shell_run(session)
# editor_tui_run(session)
```

Substring assertions on the whole file could never fail while that comment
existed, so the specs stayed green across the entire period the dispatch was
absent.

## What changed

The needles are now anchored to indented call statements
(`"        gui_shell_run(session)"`) and to `if args.contains("--gui"):`, which
a comment cannot satisfy. Both specs are consequently RED. They are correct and
must stay RED until the product is fixed — per `.claude/rules/testing.md`, a
correct spec that fails is a legitimate artifact.

## Unblock condition

Either:

1. Add the missing dispatch arms in `src/app/editor/main.spl` — a `--gui` arm
   calling `gui_shell_run(session)` and a default/`--tui` arm calling
   `editor_tui_run(session)`, both built from `_editor_session_for(args)`, in
   the same shape as the existing `--gui-sdl` arm; **or**
2. If the entrypoint deliberately must not own the interactive loops, remove
   `--gui` from `print_help()` and repoint the two specs at whatever module
   does own the dispatch (`tui_main.spl` for the TUI), stating that contract
   explicitly.

Do not resolve by relaxing the needles back to a whole-file substring match.

## Note

There are two definitions of `gui_shell_run`/`gui_shell_run_sdl`
(`src/app/editor/gui_shell.spl:53,72` and
`src/app/editor/gui_shell_core.spl:67,86`). Whichever arm is added should make
the intended owner explicit; the duplication is a separate concern.

## Resolution (2026-08-10, stream M3)

Fixed via option 1. `src/app/editor/main.spl` now has a `--gui` arm calling
`gui_shell_run(session)` and a `--tui` arm calling `editor_tui_run(session)`,
both built from `_editor_session_for(args)` and both placed AFTER the
`--log-mode=json` early-return, matching the `--gui-sdl` shape from
`9611cfb661d`. Dispatch is explicit-flag only — a bare `simple editor` and a
`--log-mode=json` probe still return promptly without entering a shell loop
(verified: the JSON probe returns immediately). `--tui` was already a known
launch mode in `src/lib/editor/core/launch.spl`, so it does not trip the
unknown-option path. The misleading "intended dispatch hooks" header comment
is gone; `print_help()` now lists `--tui` as well.

Verdicts (`src/compiler_rust/target/bootstrap/simple test --timeout 900`):

- `editor_gui_spec.spl` — the target example `supports --gui flag for GUI mode`
  now PASSES. File verdict `executed=80 passed=75 failed=5`; the 5 remaining
  failures are unrelated and pre-existing (quick-switch picker, LSP rename
  preview, and three MCP tool examples).
- `editor_buffer_spec.spl` — the target example `calls editor_tui_run with
  session` now PASSES. File verdict `executed=60 passed=56 failed=4`; the 4
  remaining failures are unrelated and pre-existing (cursor edit ops, save/
  save_as, folded header markers, normal-mode keys).

Only `test/03_system/gui/` copies of these two specs exist; there is no
`test/system/gui/` twin.
