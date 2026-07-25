# `bin/simple test` never delegates to `simple_seed` when invoked via the symlink

**Date:** 2026-07-24 · **Severity:** high (tooling) · **Status:** source fix landed; deployed binary awaits redeploy

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

`_cli_current_exe_path()` now prefers `readlink -f /proc/self/exe`
(non-Windows), falling back to the argv[0] logic. This resolves the symlink
and removes the cwd dependency; it also makes the `_cli_is_current_exe`
fork-bomb guard compare real identities. **Takes effect on the next
build/redeploy of the CLI** — the currently deployed native binary still has
the old lookup.

## Workaround until redeploy

Invoke the real path, not the symlink:
`bin/release/x86_64-unknown-linux-gnu/simple test <spec> --no-session-daemon`.

Do NOT hand-copy a seed to `bin/simple_seed` — it does not fix the empty-path
lookup, and an untracked 31 MB binary in `bin/` risks being swept into a
parallel session's whole-WC sync commit.

## Related

- `smf_stub_shadowing_unresolved_describe_2026-07-24.md` (same symptom, different cause — check `.smf` stubs first)
- `native_cli_run_std_hardware_brace_import_unresolved_2026-07-24.md` (deploy clobber that removed the sibling)
