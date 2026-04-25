# `bin/simple game` runtime dispatch needs bootstrap rebuild

**Priority:** low (script-level invocation works)
**Filed:** 2026-04-25
**Component:** `bin/simple` runtime / dispatch table
**Discovered by:** game2d-framework SStack Phase 7 verification

## Description

After adding `CommandEntry { name: "game", app_path: "src/app/game/main.spl", ... }`
to `src/app/cli/dispatch/table.spl`, the *script* path
`bin/simple src/app/game/main.spl ...` works, but the dispatched form
`bin/simple game new|run|test|inspect` requires the bootstrap binary to be
rebuilt so the new `CommandEntry` is baked into the cached `bin/simple` SMF.

This is the standard bootstrap-rebuild pattern documented in memory
`feedback_extern_bootstrap_rebuild.md` and `feedback_mcp_cache_off_by_default.md`.
The cached compiled wrapper does not pick up source-table edits until the
self-hosted compiler re-emits.

## Repro

After Phase 5 implement landed:

```
bin/simple game new hello       # dispatcher does not recognize 'game'
bin/simple src/app/game/main.spl new hello   # works (script path)
```

## Evidence

- `src/app/cli/dispatch/table.spl` — new `game` row added (Phase 5).
- State file `.sstack/game2d-framework/state.md`:
  - `### 7-verify-rerun-2 W4` item 1: "Bootstrap rebuild for `bin/simple game`
    runtime dispatch (rt_cli_run_file cfg-gated; pre-existing in
    worktree-snapshot WIP commit)".
- `src/app/game/{main,new,run,test,inspect}.spl` — five files exist on disk.

## Suggested fix direction

Run `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` (per memory
`feedback_extern_bootstrap_rebuild.md`) — *not* `bin/simple build bootstrap`,
which falls through the wrapper whitelist and silently no-ops. Verify
post-rebuild that `bin/simple game new --help` exits 0 with usage text from
`src/app/game/main.spl`.

## Related

- `doc/08_tracking/bug/game2d_render_002_gpu_pipeline_arms.md`
- `.sstack/game2d-framework/state.md` `### 5-implement` Wave-D CLI section
