# Phase 4 early front-end check: every HIR shard exits 1, claimed=0 (full-cli / interpreter)

- **Date:** 2026-10-19
- **Status:** root-caused; fix is in the check invocation (not compiler source)
- **Producer:** `scope-producer-3d9d-20261018/strict-link-preparation/simple-scope-diagnostic-strict.exe`
- **Tree:** `C:/dev/simple-p3build-20261019` @ `d862cc6b9fc` (sparse)

## Symptom

`p4check-20261019/check-one.shs full-cli src/app/cli/_CliMain/main_and_help.spl`
(2254-module closure) and the `interpreter_main.spl` closure (2255) parse 19/19
OK, then every HIR shard owner reports
`[hir-shard] owner=i/11@0 status=BLOCKED exit=1 claimed=0 sealed=0 finished=false`
and the ledger's `BLOCKED` says `incomplete worker or ledger publication`. The
same producer and flags pass HIR for `bootstrap_main.spl` (1157) and
`test_runner_new/main.spl` (261). The parent log contains nothing from the
workers.

## Reproduction of one worker

Captured the parent's real worker argv (`Win32_Process.CommandLine`) and
replayed it by hand with `SIMPLE_NATIVE_BUILD_WORKER=1`,
`SIMPLE_HIR_SHARD_QUEUE=<fresh dir>`, `SIMPLE_HIR_SHARD_OWNER=0/11@0` and the
check's env, with stdout/stderr sent to files. The worker dies in **phase 1
`load_sources`**, before it publishes the HIR inventory (so it claims nothing):

```
error: unresolved import 'os.cli' (used in .../src/app/cli/_CliMain/main_and_help.spl): no source file found for this module path relative to the working directory, src/, src/lib/, or '...'
error: unresolved import 'os.qemu_runner' (used in .../src/app/cli/_CliMain/args_and_os_commands.spl)
error: unresolved import 'os.smf.dynsmf_owned_v2' (used in .../src/compiler/99.loader/module_loader_compat.spl)
error: unresolved import 'os.smf.smf_dynlib' / 'os.smf.smf_generation' / 'os.smf.dynsmf_{session,lifecycle,trust_registry}'
error: unresolved import 'os.compositor.host_compositor_{core,entry}' / 'os.userlib.ipc_protocol'
[ERROR] phase 1 FAILED
```

11 distinct imports, all `os.*`.

## Root cause

The full CLI closure imports `src/os/**`. The check gets no `src/os` from
either side:

1. `check-one.shs` passes `--source` for compositions, compiler, app, lib and
   plugins, but **not `src/os`**. The SCV snapshot the worker compiles from
   (`build/scv/snapshots/<rev>/src/`) holds only those roots.
2. The tree it runs in, `simple-p3build-20261019`, is a sparse checkout that
   was sized for the Phase 3 `bootstrap_main.spl` closure, and it has **no
   `src/os/` at all**.

The parent's entry-closure walk does not fail on this, by design
(`_native_build_entry_closure`: "an unresolved `use` is skipped; a genuinely
missing import still errors in the compile phase"). So the parse shards pass and
the first hard failure is each HIR worker's own `load_sources`.
`bootstrap_main` and `test_runner_new` import nothing from `os.*`, which is why
they pass.

The sanctioned Phase 4 lanes already pass `--source src/os`
(`scripts/bootstrap/bootstrap-provisional-phase3-phase4.shs`,
`bootstrap-phase4-grouped.shs`, `prepare-provisional-manager-images.shs`). It
was only the ad-hoc check that left it out. No size cap, command-line length
limit or long-path problem is involved: the worker argv is 2,621 chars.

## Why the worker error was invisible

The producer's runtime predates `d61960f51f9` ("fix(runtime): preserve Windows
async child standard streams", 2026-10-18). Current source
`rt_process_spawn_async_owned_windows` duplicates the parent's std handles into
the shard child, so a producer built after that commit relays worker stderr
into the parent log. No further parent-side logging change is needed.
`process_spawn_redirected` is not a usable substitute here because it replaces
`SIMPLE_FRONTEND_CACHE_DIR`, `SIMPLE_NATIVE_BUILD_CACHE_DIR` and `TMP` with a
private scope, which would break the shard cache handoff.

## Fix

Run the check in a tree that contains `src/os` (same commit, with `/src/os/`
added to the sparse set), and add `--source src/os`:
`p4check-20261019/check-one-os.shs`.

## Verification

`check-one-os.shs`-equivalent run (`--threads 1`, one HIR worker): the HIR
worker gets past phase 1 and lowers modules (more than 1,077 claims/terminals in
`queue-43340-0`, compared with 0 before). The final aggregate line is in
`p4check-20261019/repro/full-cli-fixed.log`.
