# Compiled checker per-file transient ownership

- **Id:** `compiled_checker_multifile_rss_retention_2026-08-03`
- **Status:** fixed for non-string transient parser objects (re-verified
  2026-11-25 by source inspection — see note at bottom); residual
  process-persistent strings remain tracked separately as
  `compiled_checker_transient_string_retention_2026-08-03`
- **Severity:** P1
- **Owner:** `src/app/check/main.spl::check_one`

## Symptom and root cause

The compiled checker parsed every command-line file in one process without the
transient lifecycle used by the compiler driver. Parser-created arrays, dicts,
enums, closures, floats, and raw `rt_alloc` allocations consequently remained
registered after each file. A paired Stage 4 cycle2 sample showed near-additive
retention: the median 64-file batch RSS was 1.01 times the sum of isolated
per-file RSS above the 5.25 MiB process base.

`check_one` also returned early for SSpec guidance and error paths, so adding
cleanup to only the success path would have preserved the leak and made later
files order-dependent.

## Fix

Every existing file now enters a per-file transient scope before file read,
guidance, parse, and lint. All post-begin outcomes converge on one cleanup path:

1. `lexer_release_parse_source_globals()` drops lexer/source roots.
2. `rt_transient_array_scope_end()` reclaims file-owned transient objects.
3. `ast_reset()` recreates reusable process-lifetime arena state only after the
   scope has ended.

Scope begin/end failures fail closed. Missing-file, diagnostic ordering,
summary, JSON behavior, and exit status are otherwise unchanged.

The teardown order is load-bearing. Resetting the AST before ending the scope
would allocate the next file's arena inside the dying scope; this is prohibited
by `ast_arena_reset_inside_transient_scope_2026-08-01`.

## Regression coverage

`test/01_unit/app/check/check_multifile_transient_scope_spec.spl` covers:

- a valid file returning success;
- a parser failure;
- SSpec command-block guidance failure;
- a malformed file followed by a valid file in the same process.

The focused interpreter run passed 4/4 examples once.

## Fresh native checker measurement

A fresh x86_64 checker build compiled 46 modules with 0 failures in 22.2 s.
One bounded prefix set used the same 64 real tooling files as cycle2 batch 1;
isolated baseline inputs ranged from 34,048 to 313,076 KiB RSS.

| files | exit | wall | max RSS KiB |
|---:|---:|---:|---:|
| 1 | 1 | 0.11 s | 34,048 |
| 8 | 1 | 1.04 s | 290,224 |
| 32 | 1 | 3.05 s | 716,344 |
| 64 | 1 | 8.78 s | 2,144,728 |

The 64-file stdout and stderr SHA-256 digests exactly matched the pre-fix
cycle2 batch (`0dd8cd…` and empty `e3b0c4…`), and the exit code remained 1.
The prior max RSS was 2,219,888 KiB, so this narrow lifecycle fix reduced the
sample by 75,160 KiB (3.4%). The measured residual slope was 33,503 KiB/file
(32.7 MiB/file).

## Residual retention (not fixed here)

`runtime_native.c::rt_core_reclaim_transient_immortal` deliberately skips
strings, while `rt_string_new_uncached` allocates and registers every string as
process-persistent. Parser token text and derived diagnostic/path strings
therefore dominate the remaining slope even after non-string transient objects
are reclaimed. Fixing string ownership safely is a runtime-wide lifetime change,
not a checker-only cleanup, and is intentionally outside this pure-Simple lane.
It remains open under `compiled_checker_transient_string_retention_2026-08-03`.

## Re-verification 2026-11-25 (source inspection; spec run environment-blocked)

Inspected at `release/1.0.0` tip `47d6c5eddd5`: the per-file transient
lifecycle is present and converges every outcome on one cleanup path, with
the documented load-bearing teardown order — `checker_begin_file_scope`
(`src/app/check/main.spl:264`) runs `reset_all_pools()` + `ast_reset()`
*before* `rt_transient_array_scope_begin()`, and `checker_end_file_scope`
(`main.spl:272`) runs `rt_transient_array_scope_end()` →
`lexer_release_parse_source_globals()` → `ast_reset()` only after the scope
has ended, failing closed (poison flag) on begin/end failure. Regression
spec `test/01_unit/app/check/check_multifile_transient_scope_spec.spl` is
present with its examples intact.

Limit: the spec could not be re-executed on this Windows host — the tracked
`bin/simple.exe` (seed, last refreshed 2026-11-17 in `41dbae93225`) cannot
compile the current test-runner/lib source at any recent tree (fails first
on `@representation_boundary` at tip `cfd89933699`, and on unrelated
private-visibility errors at both `cfd89933699^` and its own commit
`41dbae93225`); fleet lanes that executed specs today used a locally
rebuilt seed, which this lane is not permitted to build. Verification here
is by code inspection only.
