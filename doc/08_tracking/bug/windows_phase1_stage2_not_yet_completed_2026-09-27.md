# Windows bootstrap phase 1: Stage 2 has never completed — state and next steps

Filed: 2026-09-27
Host: DESKTOP-5A4V03J (Windows 11, `x86_64-pc-windows-gnu`, clang/LLVM 23.1.0)
Status: OPEN. Six blocking defects were fixed (all landed); two remain.

## Where phase 1 actually gets to now

Preflight, seed publish, tool-authority bind, git/source-input audits and the
Stage 2 ADMISSION all pass reproducibly. Stage 2 compiles all 901 modules and
reaches the native link. No pure-Simple `simple.exe` has ever been produced,
so `simple test` GREEN still does not prove self-hosted on this host.

## Fixed and landed (for context, do not re-investigate)

1. `env` transiently fails to exec under memory pressure (`shell-status=125`),
   aborting the fingerprint stage. Retry, status-125 only.
2. The Stage 4 tool-authority bind aborted on the same class with a message
   naming none of its ~20 failure sites. Retry + xtrace on the last attempt.
3. The "Rust inputs changed" refusal overwrote the `pre` fingerprint details
   with the `post` ones, destroying the evidence. Details kept per phase.
4. GNU ld cannot consume `\?\` verbatim cache-root paths.
   `respell_args_for_external_tool`.
5. The windows-gnu lane never selected a linker, so clang's mingw driver used
   GNU ld. `-fuse-ld=lld` in source.
6. `resolve_defined_suffix_alias` aliased libc/winsock names to same-named
   Simple functions (`select` -> an async combinator). `PLATFORM_C_SYMBOLS`.

## Remaining blocker 1: Stage 2 memory

See `stage2_memory_grows_monotonically_with_module_count_2026-09-26.md`. The
module it dies on tracks host commit headroom (`850/901` at ~9 GiB free,
`650/901` at ~4.2 GiB, `400/901` at ~4-5 GiB under load). Commit limit here is
30.1 GiB (15.7 physical + a 14.8 GiB pagefile whose peak use hit 12.4 GiB).

Two paths, in order:
- Raise the commit limit (an explicit 20 GiB/28 GiB pagefile takes it to ~44
  GiB). Needs Administrator; `Start-Process -Verb RunAs` could not raise a UAC
  prompt from the agent session, so a human must run it. This MOVES the wall,
  it does not remove it: 901 modules only grows.
- Find the retention. No per-module RSS curve has been captured yet; that
  measurement is the honest next step, not a guess at the culprit.

Note `--jobs=N` is ONE knob for both `CARGO_BUILD_JOBS` and the Stage 2 native
build jobs (CLI overrides `SIMPLE_NATIVE_BUILD_THREADS`), so raising it to speed
the ~27-minute seed rebuild also multiplies Stage 2's concurrent working sets.
Raise it only after the commit limit is raised.

## Remaining blocker 2: the LLD crash the alias guard should have removed

See `lld_231_crashes_on_generated_compat_alias_archive_2026-09-27.md`. With
`PLATFORM_C_SYMBOLS` in place the `select` alias should no longer be generated,
so this link should proceed — **but that has not been observed yet.** The run
that would have shown it was still in its seed rebuild when this session ended.
Verify before assuming it is resolved.

The LLD-side defect is real and unreported upstream: a linker must diagnose a
symbol conflict, not segfault. A reduced case is still to be built.

## Operational notes worth keeping

- Do NOT edit any tracked file while a full bootstrap runs. The publish-time
  fingerprint compares pre/post and refuses; a markdown edit at 15:20 aborted a
  27-minute rebuild. (That a doc counts as a "Rust seed input" looks over-broad
  and may deserve its own record; one observation only so far.)
- Do NOT reorder PATH so LLVM precedes mingw-winlibs. It changes the resolved
  `cc-*` identity between the pre and post fingerprint observations and the
  publish refuses with `category_native_tools_sha256` differing. Three runs were
  lost to this. `-fuse-ld=lld` makes the reorder unnecessary.
- `SIMPLE_LINKER` cannot be set from outside: the bootstrap's env scrub drops
  every `SIMPLE_*` except three session vars, so it never reaches the Stage 2
  compiler, and it perturbs the same fingerprint.
