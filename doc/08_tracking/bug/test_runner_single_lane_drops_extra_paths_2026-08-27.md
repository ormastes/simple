# `--no-session-daemon` silently drops every spec path after the first (false green)

- **Date:** 2026-08-27
- **Status:** FIXED (fix + fail-closed guard landed in this change)
- **Severity:** High — a silent false green in a real, documented runner lane
- **Component:** `src/app/test_runner_new/test_runner_single.spl`

## Symptom

```
$ bin/simple test --no-session-daemon text_helpers_spec.spl collection_helpers_spec.spl
Results: 95 total, 95 passed, 0 failed
PASS test/01_unit/lib/std/common/text_helpers_spec.spl
$ echo $?
0
```

`collection_helpers_spec.spl` is a **genuinely failing** spec. It was never run,
never mentioned, and never counted. The same invocation **without**
`--no-session-daemon` correctly reports it:

```
Results: 95 total, 95 passed, 0 failed
PASS test/01_unit/lib/std/common/text_helpers_spec.spl
Results: 1 total, 0 passed, 1 failed
FAIL test/01_unit/lib/std/common/collection_helpers_spec.spl
$ echo $?
1
```

So the single-file lane turns a red run green. This is exactly the class this
repo's verdict convention forbids: *a run that checked nothing (here: checked
less than it was asked to) is ERROR, never a pass* (`.claude/rules/vcs.md`).

## Root cause

`parse_child_run` (`test_runner_single.spl:138`) kept only the FIRST positional
argument and dropped the rest **in silence**:

```
if not arg.starts_with("-") and path == "":
    path = arg
```

Every later positional path fell through the `while` loop with no branch, no
warning, and no effect on the exit code. `main()` then executed the one path it
had, saw `failed == 0`, and returned 0.

Note this lane is otherwise *heavily* hardened against greenwash — it carries
dedicated fail-closed branches for timeouts, death-by-signal, zero-executed
specs, truncated child output and forged evidence. All of that hardening is
per-file, and none of it can fire for a file the parser threw away before any
of it ran.

## Relation to the previously documented trap

`.spipe/simply_showcase/state.md` records `--timeout` *together with*
`--no-session-daemon` as making the runner "process only the FIRST path and exit
0". That attribution is **wrong and under-scoped**: `--timeout` is irrelevant.
Measured on `origin/main` @ `287cb32cd09`, plain `--no-session-daemon` with two
paths drops the second identically. The trigger is the lane, not the flag pair.

## Not reproduced (ruled out)

The originating report described `bin/simple test <spec>` exiting 0 with no
verdict at all. That did not reproduce in a fresh detached worktree off
`origin/main`, nor in the shared worktree:

- `test/01_unit/std/common/text_helpers_spec.spl` — the path in the report — does
  not exist (real path has a `lib/` component). Both worktrees answer
  `error: test file not found` with **rc=1**.
- A nonexistent *directory* target answers `Results: 0 total` + `No tests
  selected` with **rc=4**.
- The correct spec path runs 95 examples and emits both `Results:` and
  `SPEC FILE VERDICT:` with rc=0 (the verdict is mid-stream, followed by
  compiler warnings — tailing the output hides it, which likely explains the
  "no verdict line" observation).

Stdlib resolution was verified to come from the worktree's own `src/`, so the
foreign-`CARGO_MANIFEST_DIR` hazard was not in play either.

## Blast radius

**No current CI/gate green is invalidated.** Every in-tree caller of
`--no-session-daemon` passes exactly one path: the daemon adapters
(`src/app/test_daemon/adapters/*.spl`, `daemon.spl`, `light_daemon.spl`,
`agent_client.spl`), `test_runner_client.spl:465`, and every
`scripts/check/*.shs` invocation (checked: nvme, llm-caret, 2d-renderdoc,
vulkan, bootstrap-smoke, outcome-exits, local-container — all single-path,
several looping one spec at a time).

The exposure is **interactive and agent-driven**: any human or agent that batches
several specs onto one `--no-session-daemon` command reads exit 0 as "all
green" while only the first file ever ran. Given how many skills and docs
recommend that flag for daemon-free runs, that is a live greenwash channel.

## Fix

`test_runner_single.spl:parse_child_run` now collects extra positional paths and
returns `valid: false` with an explicit error naming them, so `main()` exits 1:

```
error: single-file lane accepts exactly one test file; refusing to silently
drop 1 more (…collection_helpers_spec.spl) — drop --no-session-daemon to run
multiple files: …text_helpers_spec.spl
```

Refusing (rather than running them all) is deliberate and minimal: this lane is
single-file by design and is spawned as a child with one path by every real
caller. The multi-path capability already exists correctly on the default lane.

The parser also uses an explicit one-value option table before classifying
positionals. This preserves forwarded pairs such as `--format json` and
adapter-owned `--qemu-socket <socket>` without weakening the multiple-path
guard: boolean flags consume no following token, so a real second path still
fails closed. Consumption is conditional on validation: empty values and a
following option token are missing values, `--format` accepts only
`text|json|doc`, and numeric options require a numeric value. Both separated
and `--option=value` forms use the same validation, so malformed option syntax
cannot disguise a second path.

## Specs

- **Reproducer:** `test/01_unit/app/test_runner_new/single_lane_extra_paths_spec.spl`
  — asserts `parse_child_run([a, b])` is `valid: false`, names the dropped path,
  and still reports the first. Verified RED before the fix
  (`Results: 5 total, 3 passed, 2 failed`, exit 1) and GREEN after
  (`5 total, 5 passed`, exit 0).
- **Generalization:** `test/01_unit/app/test_runner_new/single_lane_arg_parsing_neighbors_spec.spl`
  — walks the adjacent argv shapes (extra path interleaved between flags,
  `--timeout=` form, three paths, the same path twice) plus the
  already-fail-closed classes (no path, non-`.spl`, nonexistent `.spl`) and the
  single-path/`--list` contracts. It also covers separated `--format` values
  before and after the path, an adapter-forwarded QEMU socket, a real second
  path after a format pair, missing option values, malformed separated and
  equals-form format values before a second path, numeric-domain rejection,
  option-token rejection, and a valid signed decimal. `22 total, 22 passed`.

## Guard

`scripts/check/check-test-runner-single-lane-paths.shs` — fail-closed, verdict
as the last line of stdout, fatal `--selftest`, 0 invocations is `ERROR` never a
pass. Four probes: two paths bare, two paths with `--timeout` (the documented
trap shape), a single-path non-regression case so the fix cannot degenerate
into "reject everything", and a successful single path with `--format json`.

Verified as a real ratchet, not a tautology:

- with the fix reverted: `FAIL — 4 invocation(s) executed, false green(s):
  --no-session-daemon(2 paths, rc=0) --no-session-daemon --timeout(2 paths, rc=0)` (exit 1)
- with the fix applied: `PASS — 4 invocation(s) executed, 0 false green(s)` (exit 0)

## Pre-existing unrelated red

`scripts/check/check-test-runner-outcome-exits.shs` fails on `origin/main`
@ `287cb32cd09` with `error: expected .spl test file: build/…/empty`. Confirmed
byte-identical before and after this change — not caused by, and not fixed by,
this work.
