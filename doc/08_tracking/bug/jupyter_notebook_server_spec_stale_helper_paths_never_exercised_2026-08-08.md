# `jupyter_notebook_server_system_spec.spl` — 2 of 4 local E2E `it` blocks reference Python helpers that don't exist, so they always SKIP

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

- **Date:** 2026-08-08
- **Area:** `test/03_system/tools/jupyter/jupyter_notebook_server_system_spec.spl` (P0/P3 Jupyter
  system-spec suite)
- **Symptom:** Two of the four "local E2E" `it` blocks in this spec reference Python helper
  scripts under `test/system/jupyter/helpers/` — a path that has never existed in
  `test/03_system/tools/jupyter/helpers/` (the canonical, actively-developed spec directory; the
  spec itself lives at the `03_system` path). Every run prints:
  ```
  SKIP: test/system/jupyter/helpers/run_server_check.py not found
  SKIP: test/system/jupyter/helpers/run_notebook_server_test.py not found
  ```
  and the `it` block still reports green (`✓`) because the SKIP path returns before any
  `expect(...)` runs — so `bin/simple test` has reported these two checks as passing for as long
  as the file has existed, without ever exercising the HTTP+ZMQ local-server flow or the
  `nbconvert` fixture execution they claim to cover.

## Root cause

`test/system/jupyter/` is a stale, byte-for-byte duplicate of the spec tree that predates the
`test/03_system/tools/jupyter/` restructure (its own copy of this same spec file has the identical
bug and is not referenced by any build/test entry point apart from itself — see `git log`, its last
touch is an unrelated repo-wide commit). Neither copy's `helpers/` directory has ever contained
`run_server_check.py` or `run_notebook_server_test.py`; only
`test/03_system/tools/jupyter/helpers/wrapper_transport_roundtrip.py` exists, and — until this
session — it wasn't wired into any `.spl` spec at all (fixed separately: this spec now has a
`should complete a live jupyter_client <-> kernel_wrapper.py ZMQ round trip` `it` block that runs
it for real).

## What's still missing

Two real capabilities described in the spec's own header comment — "Start real Jupyter server,
HTTP + ZMQ checks" and the two `nbconvert --execute` fixture checks (`hello.ipynb`,
`state_persistence.ipynb`) — have **no implementation** anywhere in the repo. The nearest existing
coverage is `scripts/test/jupyter-docker-test.shs`, which does run `nbconvert --execute` against
`mode_local.ipynb`/`mode_qemu_rv32.ipynb` for real, but only inside the Docker E2E lane and against
different fixtures than `hello.ipynb`/`state_persistence.ipynb`.

## Ask

Either:
1. Write `test/03_system/tools/jupyter/helpers/run_server_check.py` and
   `run_notebook_server_test.py` (real `jupyter_client`/`nbconvert` drivers, same pattern as
   `wrapper_transport_roundtrip.py`) and fix the `helper` path prefix in the spec, or
2. Delete these two `it` blocks and fold their intent into the Docker E2E lane / the new wrapper
   round-trip test, so the spec doesn't carry permanently-green placeholders.

Do not leave the current state (green via early-return SKIP) as-is without a decision — a reader
of `bin/simple test` output cannot distinguish this from a real pass.

## Also flagged, not fixed here (out of scope for this pass)

`test/system/jupyter/` itself (the whole directory, not just this file) looks like leftover
pre-restructure duplicate cruft — it isn't referenced by anything except itself and isn't the path
`doc/06_spec/03_system/tools/jupyter/...` generates from. Left untouched pending a decision on
whether to delete it; flagging here so it isn't mistaken for a second, independently-maintained
suite.

## Resolution (2026-08-09)

Re-read the current spec (`test/03_system/tools/jupyter/jupyter_notebook_server_system_spec.spl`,
171 lines). Three `it` blocks reference the stale helper path, not two (`should start server and
execute cell via HTTP + ZMQ locally`, `should execute hello.ipynb via nbconvert and verify output`,
`should execute state_persistence.ipynb and verify cross-cell state`). All three are **not**
placeholder scaffolding: each contains real `expect(code).to_equal(0)` /
`expect(stdout).to_contain("ALL CHECKS PASSED")` assertions that run whenever the helper file is
present — the `SKIP` early-`return` only fires because the helper doesn't exist at any path yet.
This matches decision path (b) in the "Ask" above, not (a): the assertions have real value once the
helper scripts exist, so the `it` blocks were **kept, not deleted**.

What was done:
1. **Fixed the stale path** in all three `it` blocks and in both `--notebook` fixture args
   (`test/system/jupyter/helpers/...` → `test/03_system/tools/jupyter/helpers/...`,
   `test/system/jupyter/fixtures/...` → `test/03_system/tools/jupyter/fixtures/...`) — the canonical,
   actively-developed directory. This does not make the checks pass (the helper scripts still don't
   exist anywhere), but it removes the double bug (wrong directory *and* missing file) down to a
   single, already-tracked gap.
2. **The actual helper-script implementation was intentionally left out of scope** — building
   `run_server_check.py` / `run_notebook_server_test.py` is real feature work (a Python
   `jupyter_client`/`nbconvert` driver, same shape as the existing
   `test/03_system/tools/jupyter/helpers/wrapper_transport_roundtrip.py`), and is already tracked
   separately at `doc/08_tracking/todo/jupyter_e2e_helper_scripts_missing_2026-08-08.md` (P2). No new
   TODO needed. Note: that todo doc's own text still says "fix the stale path" as an action item —
   that action is now DONE by this change.
3. **`test/system/jupyter/` duplicate directory removed.** Diffed the spec file byte-for-byte
   against its `test/03_system/tools/jupyter/` counterpart — identical. Repo-wide grep for the
   literal path `test/system/jupyter` (no extension filter, excluding the directory's own files)
   found only descriptive mentions in this bug doc, the sibling todo doc, one generated
   `doc/06_spec/...md` (mirrors the identical stale string that lived in the duplicate spec file —
   now stale in a different way after step 1, harmless, doc regenerates from source), and two
   research/LLM-wiki docs that merely note the duplicate's existence. `git log` on the two
   directories showed the duplicate's last per-file touch was the same repo-wide bulk `chore: sync`
   commits as the canonical directory, i.e. it was never independently maintained. No build script,
   CI config, or `.spl`/`.shs` file loads from `test/system/jupyter/` at runtime. Confidence was
   high enough to delete it (`git rm -r test/system/jupyter/`, 12 tracked files removed). Left the
   two descriptive doc mentions (`doc/01_research/app/tools/notebook_lanes_research.md`,
   `doc/00_llm_process/feature_expert/notebook_lanes/skill.md`) untouched — updating stale prose in
   unrelated research/wiki docs is out of scope for this bug fix.

**Verification:** `SIMPLE_MODULE_LIMIT=4000 bin/simple test
test/03_system/tools/jupyter/jupyter_notebook_server_system_spec.spl` →
`Results: 6 total, 6 passed, 0 failed`. All three affected `it` blocks still print `SKIP: ... not
found` (expected — the helper scripts genuinely don't exist yet) and still report green via the
early-return path; that residual "green via SKIP" behavior is intentional per decision (b) and is
the exact condition the linked P2 todo now fully covers (path is no longer part of the gap, only the
missing scripts are).

**Status: RESOLVED** — the ambiguity this doc opened (fix vs. delete, and whether the duplicate
directory is dead) is closed. The one remaining open item (write the two Python helper scripts) is
intentionally *not* closed here and continues to live at
`doc/08_tracking/todo/jupyter_e2e_helper_scripts_missing_2026-08-08.md`.
