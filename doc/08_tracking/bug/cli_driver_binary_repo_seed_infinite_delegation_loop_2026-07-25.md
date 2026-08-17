# Bug: `bin/simple run` infinite delegation loop — blocks ALL execution

**Date:** 2026-07-25
Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
lane (`doc/08_tracking/bug/wm_showcase_no_headless_lane_2026-07-25.md`); files
as its own defect because it blocks every `bin/simple run`/`bin/simple lint`
invocation on this host, not just the headless-lane work.

## Symptom

`bin/simple run <any .spl file>` — including a trivial `fn main(): print
"hello"; 0` — never reaches user code. It spins printing:

```
simple: seed sibling not found, skipping delegation: /usr/bin/simple_seed
```

repeatedly, forever (verified up to 90s wall-clock with zero other output).
`bin/simple lint <file>` fails immediately with `error: field access on nil
receiver` — consistent with the same code path crashing instead of looping,
depending on entry point.

## Proof it's a genuine infinite loop (not one large one-shot dump)

Output size scales ~linearly with wall-clock time, ruling out a bounded
"print once per module" explanation:

| timeout | bytes captured |
|--------:|----------------:|
| 3s | 9,344 |
| 6s | 19,418 |
| 12s | 53,801 |

Reproduced identically against both `bin/release/x86_64-unknown-linux-gnu/simple`
(the newer Jul 25 binary) and `release/x86_64-unknown-linux-gnu/simple` (the
binary `bin/simple` currently symlinks to, built Jul 7) — this is not specific
to one deployed artifact.

## Root-cause hypothesis (not yet fixed)

`src/app/io/cli_ops.spl`, `pub fn _cli_driver_binary()` (around line 236-260):

```
if not _cli_is_windows_platform():
    val exe_path = _cli_current_exe_path()
    if exe_path.len() > 0:
        val seed_sibling = _cli_seed_sibling_path(exe_path)
        if _cli_file_exists_impl(seed_sibling):
            if not _cli_is_current_exe(seed_sibling):
                return seed_sibling
        else:
            val repo_seed = _cli_repo_seed_path()
            if repo_seed.len() > 0:
                return repo_seed          # <-- NO self-exec guard here
            _cli_eprint("simple: seed sibling not found, skipping delegation: {seed_sibling}")
```

Every other return path in this function (the `override` branch at the top,
and the `bin/simple{ext}` candidate at the bottom) is wrapped in
`_cli_is_current_exe(...)` self-exec guard, with an explicit comment
referencing a prior fork-bomb incident ("simple.bak fork bomb OOM-killed the
user session, 2026-06-12"). The `repo_seed` branch added later has **no such
guard**. If `_cli_repo_seed_path()` resolves to a path that IS (or execs into)
the current binary in this repo layout, `_cli_driver_binary()` returns it,
`cli_run_file`/`cli_run_code` (`src/app/io/_CliCommands/run_commands.spl:68,100`)
spawn it as a child process via `process_run_inherit`/`_cli_process_run`, the
child recomputes the same `_cli_driver_binary()` and recurses — an unguarded
self-exec loop, matching the exact failure class the sibling branches were
already patched against. This is a hypothesis pending confirmation (did not
instrument `_cli_repo_seed_path()` directly — blocked by the same hang), filed
now because it fully blocks verification work and matches the documented
incident pattern precisely.

## Impact

- Cannot run **any** `.spl` file via `bin/simple run` (interpreter or
  `--mode=interpreter`) on this host right now.
- Cannot use `bin/simple lint` either (crashes on nil receiver instead, same
  area).
- Directly blocked: real-evidence verification of the host-WM headless capture
  lane added in `examples/06_io/ui/wm_widget_showcase_gui.spl`,
  `wm_graphics_2d_showcase_gui.spl`, `wm_web_standards_showcase_gui.spl` (see
  the headless-lane bug doc above) — the new `SIMPLE_WM_HEADLESS_CAPTURE=1`
  code path was written by reusing already-proven-working primitives
  (`compose_pixels`, `blit_child_frame_pixels`, `encode_ppm_p6`,
  `file_write_bytes` — all copied from code that already ships and runs in
  this file and in `web_render_file_gui.spl`), but could not be exercised
  end-to-end because the interpreter never starts.

## Workarounds tried (did not unblock)

- `SIMPLE_BOOTSTRAP_DRIVER=<path to bin/simple itself>` (should hit the
  existing self-exec guard on the override branch and return `""`, forcing
  the in-process `interpret_file()` fallback): stopped the eprint spam, but
  then hung silently for 90s with zero output — a second, separate stall in
  the in-process fallback path, not investigated further (out of scope / time
  budget for this task).
- `--mode=interpreter` flag: no effect, same infinite loop.

## Suggested next step

Add the same `_cli_is_current_exe(repo_seed)` guard already used on the other
two branches of `_cli_driver_binary()`, then re-verify with the linear-scaling
repro above (bytes vs. timeout should stop growing once the guard fires).

## 2026-08-17 reproduction attempt (CLI lane) — NOT REPRODUCED

Classified by CONTENT, not by SHA.

Empirical: `SIMPLE_EXECUTION_MODE_RECEIPT=1 bin/simple run <tmp>/hello.spl`
completed normally, `rc=0`, printing `hi`. No delegation loop, no fork bomb,
no unbounded recursion.

Current source already carries the two guards this bug needed
(`src/app/io/cli_ops.spl`):

- `_cli_is_current_exe()` (line 205-219) canonicalizes BOTH sides via
  `_cli_resolve_symlink()` before comparing, and fails CLOSED (returns `true`,
  i.e. "this is me, do not delegate") when identity cannot be established
  (line 209-212).
- `_cli_driver_binary()` (line 243-289) applies that guard at all three exits:
  the `SIMPLE_BOOTSTRAP_DRIVER` override (259), the seed sibling (271), and the
  `bin/simple` candidate (287). The repo-seed fallback (`bin/simple_seed`,
  `_cli_repo_seed_path()` line 199) is only reached when the sibling does not
  exist, and its result still flows through callers that are self-exec guarded.

Verdict: **ALREADY-FIXED / NOT-REPRODUCED**. No patch applied.
