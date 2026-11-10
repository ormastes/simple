# C-runtime compile gate RED: rt_browser_renderer_namespace_selfcheck.c

Status: OPEN. Filed 2026-08-18.

`sh scripts/check/check-c-runtime-compiles-push.shs` currently reports
`FAIL — 1 file(s) failed to compile: src/runtime/test/rt_browser_renderer_namespace_selfcheck.c (103 compiled clean, 2 skipped...)`.

Timeline evidence: the same gate reported `PASS — 104 file(s) compiled, 0
errors (2 skipped...)` earlier on 2026-08-18 (C-MIG-0013 deletion
verification). The dead-C deletion agent hit the FAIL later the same day and
proved by A/B (change removed → identical failure) that its own deletions are
NOT the cause — the file was broken in between by another session's edit.

Impact: this gate is one of the mandatory pre-push guards, so pushes touching
src/runtime/ will (correctly) block until fixed. Note the file is a TEST
fixture (`src/runtime/test/`), related to `rt_browser_renderer_preinit_active_for_test`
(a cross-TU extern retained as STILL_UNCERTAIN in the dispatch-dead audit).

Wanted: whoever owns the recent browser-renderer edit fixes the fixture; fix
ships with a reproduce check per the Fix test standard
(doc/03_plan/infra/binary_runtime_hardening/plan.md).

## 2026-11-10 status — P3 runtime-lane triage (worktree simple-p3-rt-20261110)

**Verdict: SUPERSEDED — the named fixture compiles clean at base
1504212d788b; the gate-RED state was fixed by another lane.** Fix commit:
`bd6ba8faae70 fix(runtime): browser-renderer namespace selfcheck compiles to an
empty TU until its two never-implemented functions exist` (the fixture now
compiles to an empty TU behind the two never-implemented functions).

Evidence (windows-lane-compile, pinned clang
`C:/Users/yoon/.simple/toolchains/llvm-mingw-20260922-ucrt-x86_64/bin/clang.exe`):

- `clang -fsyntax-only -I src/runtime -I src/runtime/include
  src/runtime/test/rt_browser_renderer_namespace_selfcheck.c` → exit 0.
- Full-tree `sh scripts/check/check-c-runtime-compiles-push.shs` at the same
  base: the file is ABSENT from the 28-name FAIL list (295 compiled clean,
  56 skipped for external SDKs, 28 failed — every one of the 28 is a
  POSIX-gated or ARM-intrinsic TU such as `bitmap_neon.c`,
  `runtime_bootstrap_linux_provider.c`, `stage3_fdwalk.c`; expected
  Windows-host noise for a Linux-family pre-push guard).

Side finding (OUTSIDE this assignment's six bugs — reported, not fixed):
`src/runtime/test/async_driver_iocp_smoke_selfcheck.c` FAILs this gate on any
Windows host: it includes `"async_driver.h"` (lives at
`src/runtime/platform/async_driver.h`), which is not reachable from the gate's
include set (`-I src/runtime -I src/runtime/include`); on Linux/Darwin the
include is preprocessed away inside `#if defined(_WIN32)` so the file compiles
there. Minimal fix would be qualifying the include as
`"platform/async_driver.h"` in the fixture. Left for its owner lane.

No `src/runtime` change made by this triage.

## 2026-11-11 status — P3 rt2 lane triage (worktree simple-p3-rt2-20261111)

**Verdict: SUPERSEDED-by-prior-lane** — spot-check corroborates the
2026-11-10 p3-rt addendum; no deep triage redone.

Spot-check at this lane's base (790b54f7c4fc):

- `clang -fsyntax-only -I src/runtime -I src/runtime/include
  src/runtime/test/rt_browser_renderer_namespace_selfcheck.c` (pinned
  llvm-mingw 20260922 clang) → exit 0. The fixture still compiles clean.
- Fix commit `bd6ba8faae70` (empty-TU behind the two never-implemented
  functions) is an ancestor of this base.
- seed-smoke (refreshed seed 0791c2b7f4a7): `bin/simple.exe test
  test/00_quick/spec_it_accumulation_probe.spl --mode=interpreter
  --no-cache` → 5 total, 1 passed, 4 failed — exactly this deliberately-RED
  probe's documented expected outcome on fixed code (spec-it accumulation
  P0 fix holds on the refreshed seed).

Side observation carried from the prior addendum (out of assignment scope):
`src/runtime/test/async_driver_iocp_smoke_selfcheck.c` still includes
`"async_driver.h"` unqualified, unreachable from the gate's include set on
Windows; left for its owner lane. No change made.
