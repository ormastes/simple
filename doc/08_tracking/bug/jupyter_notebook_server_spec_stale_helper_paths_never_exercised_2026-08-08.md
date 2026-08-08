# `jupyter_notebook_server_system_spec.spl` — 2 of 4 local E2E `it` blocks reference Python helpers that don't exist, so they always SKIP

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
