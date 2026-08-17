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

## 2026-08-17, second pass (dedicated lane) — PARTIALLY FIXED, guard added

### The earlier NOT-REPRODUCED verdict above is not sound evidence

`bin/simple run <hello.spl>` completing with `rc=0` does **not** exercise the
suspect code. The deployed `bin/simple`
(`bin/release/x86_64-unknown-linux-gnu/simple`, 59,536,728 bytes, Aug 16 22:59)
self-identifies as a **Rust bootstrap seed**, and the loop's marker string
exists in exactly one place in the tree:

```
$ /usr/bin/grep -rn "seed sibling not found" --include=*.rs --include=*.spl src/
src/app/io/cli_ops.spl:277
```

Zero hits under `src/compiler_rust/**`. The seed has no such delegation logic,
so a green seed run says nothing about `_cli_driver_binary()`. Any future
re-triage of this bug must drive `src/app/io/cli_ops.spl` directly.

### Driving the real path

Probe (`use app.io.cli_ops.{_cli_driver_binary, cli_current_exe_path}`), run
under interpretation from the repo root:

```
exe=[/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple]
simple: seed sibling not found, skipping delegation: .../simple_seed
driver=[]
```

### Exact delegation chain, and where the cycle closes

1. `cli_run_file` / `cli_run_code`
   (`src/app/io/_CliCommands/run_commands.spl:68,100`) ask
   `_cli_driver_binary()` for a binary and, if non-empty, spawn it as a child
   via `process_run_inherit` / `_cli_process_run`.
2. `_cli_driver_binary()` has four exits: `SIMPLE_BOOTSTRAP_DRIVER` override
   (259), seed sibling (271), **repo seed `bin/simple_seed` (274-276)**, and the
   `bin/simple{ext}` candidate (287).
3. The cycle closes at the `bin/simple` candidate: `bin/simple` is a symlink to
   `bin/release/<triple>/simple`, i.e. to the running process itself, so
   returning it means spawning ourselves, which recomputes the same value —
   unbounded, one eprint per generation, which is exactly the linear
   bytes-vs-timeout scaling recorded above.
4. **That exit is now correctly guarded** and is why the loop no longer
   reproduces. `_cli_is_current_exe()` (205-219) canonicalizes the *candidate*
   too via `rt_path_absolute` (`std::fs::canonicalize`), so the relative
   `bin/simple` resolves to the absolute release binary and matches
   `/proc/self/exe`; measured `driver=[]` confirms it fires. It also fails
   CLOSED (returns `true`) when identity cannot be established (209-212). The
   original hypothesis in this doc blamed the repo-seed branch for the observed
   loop; that was wrong — the loop ran through the `bin/simple` branch, whose
   candidate-side canonicalization had been dropped on 2026-07-24 and restored
   on 2026-07-25.

### What was still unguarded, and was fixed

The `repo_seed` exit (274-276) was the one remaining exit with **no**
`_cli_is_current_exe` check — the asymmetry this doc originally flagged is real,
even though it was not the cause of the 2026-07-25 loop. `_cli_repo_seed_path()`
(199) tests the **cwd-relative** path `bin/simple_seed`, so it names whatever
`bin/simple_seed` sits next to the current working directory; in a deploy layout
that can be a symlink onto the running executable, reopening the same fork bomb.
Fixed by adding the guard, symmetric with the other three exits.

Not currently live on this host: neither `bin/simple_seed` nor the sibling
`bin/release/x86_64-unknown-linux-gnu/simple_seed` exists, which is why control
reaches the eprint at 277 and then the (guarded) `bin/simple` candidate.

Regression check after the edit, from the repo root: probe still prints
`driver=[]`, `bin/simple run hello.spl` still prints `hi` — no behavior change
on the live path, which is the intent (the guard can only ever turn a
delegate-to-self into the in-process `interpret_file()` fallback).

### Not a contributor to today's other symptoms

Asked whether this explains the 45-minute zero-result test run and the
`reason=daemon-no-response` timeout: **no**, on two independent grounds — the
deployed binary is a Rust seed that never executes `cli_ops.spl` at all, and
even when the pure-Simple path IS driven, `_cli_driver_binary()` measurably
returns `""` (no child spawned). No shared root cause with
`deployed_seed_test_runner_init_hang_2026-07-17.md` was found via this path.

Status: the P1 hang is not reproducible and its cycle-closing exit is guarded.
Remaining follow-up is a regression spec pinning all four exits of
`_cli_driver_binary()` against self-delegation; the repo-seed branch is not
unit-testable as written (`_cli_repo_seed_path()` is private and hardcodes a
relative path), so the guard here is verified by construction plus the
no-regression run above, not by a spec.
