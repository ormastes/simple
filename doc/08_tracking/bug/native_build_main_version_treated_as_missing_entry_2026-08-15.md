# Native-build tool rejects --version as a missing entry

**Status:** fixed in the frozen Phase-4 worktree; rebuilt-tool verification pending.
**Observed:** 2026-08-15.

The Rust-seed-built `native_build_main --version` exited 1 and printed `No entry
point specified`. The retained evidence is
`build/mini_builds/phase4_tools_rust_seed/fresh/native_build_main.version.log`.

The fault is in the pure-Simple lightweight wrapper, not Rust dispatch:
`src/app/cli/native_build_main.spl` handled empty arguments and help before its
entry requirement, but omitted the standard `-V`/`--version` terminal action.
The entry guard therefore misclassified version as a build request.

The wrapper now handles both version spellings before entry validation and
prints the shared `bootstrap_version()` identity. The source contract test
locks ordering and both spellings. No fallback or fake entry is introduced.

Provider token usage and comparable completed-bug average: unavailable.
