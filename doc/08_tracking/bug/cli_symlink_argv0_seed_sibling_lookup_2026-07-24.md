# `bin/simple test` never delegates to `simple_seed` when invoked via the symlink

Status: DUPLICATE of cli_driver_binary_symlink_argv0_2026-07-11.md
Status re-verified 2026-08-17 by source inspection (triage shard 00).

**Date:** 2026-07-24 (corrected 2026-07-25) · **Severity:** high (tooling) · **Status:** source fix landed (`6cf217f0febb`); deployed binary awaits redeploy

## Symptom

With a valid `simple_seed` sibling present in `bin/release/<triple>/`,
`bin/release/<triple>/simple test <spec>` works — but the same invocation
through the `bin/simple` symlink fails every spec with
`unresolved name: describe`, and stderr shows
`seed sibling not found, skipping delegation:` with an **empty path** after
the colon.

## Root cause

`_cli_current_exe_path()` (src/app/io/cli_ops.spl) derives the executable
path from argv[0]. Under the symlink, spawned inner runners end up in the
`_cli_find_on_path` branch (strace shows `which bin/simple`; no
`simple_seed` path is ever stat'ed), yielding an exe path with no directory
component — so `_cli_seed_sibling_path` returns `""` and delegation is
skipped. argv[0] is simply not a reliable identity: it is relative,
symlinked, and cwd-dependent.

## Fix

`_cli_current_exe_path()` now prefers the kernel's `/proc/<pid>/exe` record
(non-Windows), falling back to the argv[0] logic. This resolves the symlink
and removes the cwd dependency; it also makes the `_cli_is_current_exe`
fork-bomb guard compare real identities. **Takes effect on the next
build/redeploy of the CLI** — the currently deployed native binary still has
the old lookup.

### Correction 2026-07-25 — the first form of this fix was itself broken

The original fix shipped `rt_process_run("readlink", ["-f", "/proc/self/exe"])`.
That is wrong: `/proc/self` resolves in the **spawned child**, so it returned
`/usr/bin/readlink` (and `/bin/sh` for the `shell(...)` variants) — never our
own binary. The consequence was strictly worse than the bug it fixed: the seed
sibling became `/usr/bin/simple_seed`, which never exists, so the code fell
through to delegate to `bin/simple` = itself. `bin/simple run <file>` became an
unbounded self-delegation loop (239 KB of stderr in 2 min, zero progress).

Corrected to read the link through the child's view of us:

```
rt_process_run("sh", ["-c", "readlink -f /proc/$PPID/exe"])
```

Verified empirically: `/proc/self` → `/usr/bin/readlink`; `/proc/$PPID` → the
real binary path. Because the `$PPID` hop is only correct when the helper is
exactly one level down, `_cli_is_spawned_helper_exe` now rejects a result whose
basename is `readlink`/`sh`/`dash`/`bash` and reports "identity unknown"
(fall back to argv[0]; the driver guard refuses delegation) rather than acting
on a wrong path.

Applied at all four sites that had the same trap:
`src/app/io/cli_ops.spl`, `src/compiler/80.driver/driver_public_shared.spl`,
`src/app/cli/cli_helpers.spl`,
`src/compiler/70.backend/backend/runtime_compiler.spl`.
Regression case: `test/01_unit/app/io/cli_argv0_resolution_spec.spl`
("resolves our own exe, not the spawned readlink helper").
Landed `6cf217f0febb`.

**Any `/proc/self/*` read performed by a spawned helper describes the helper.**
Passing the literal string `/proc/self/exe` as an exec *target* is fine (the
forked child is still a copy of us at exec time) — that is why
`test_runner_client.spl` and `light_daemon.spl` are correct as written.

## Workaround until redeploy

~~Invoke the real path, not the symlink:
`bin/release/x86_64-unknown-linux-gnu/simple test <spec> --no-session-daemon`.~~
**No longer valid as of 2026-07-25.** The deployed binary carries the broken
`/proc/self` form, so it self-delegates no matter which path invokes it —
identity resolution never depends on argv[0] in that build. Until redeploy,
drive the seed directly:
`bin/release/x86_64-unknown-linux-gnu/simple_seed run <file>`
(expect the "bootstrap seed only" banner; the seed is older and reports some
false-positive generics diagnostics on `lint`).

Do NOT hand-copy a seed to `bin/simple_seed` — it does not fix the empty-path
lookup, and an untracked 31 MB binary in `bin/` risks being swept into a
parallel session's whole-WC sync commit.

## Related

- `smf_stub_shadowing_unresolved_describe_2026-07-24.md` (same symptom, different cause — check `.smf` stubs first)
- `native_cli_run_std_hardware_brace_import_unresolved_2026-07-24.md` (deploy clobber that removed the sibling)
