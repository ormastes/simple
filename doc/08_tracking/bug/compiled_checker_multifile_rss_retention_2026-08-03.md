# Compiled checker per-file transient ownership

- **Id:** `compiled_checker_multifile_rss_retention_2026-08-03`
- Status: **FIXED** — verified 2026-08-21 (bug-status-consistency audit): the per-file transient scope is live at `src/app/check/main.spl:192/198` with fail-closed begin/teardown at `:226/:261`, and the regression spec `test/01_unit/app/check/check_multifile_transient_scope_spec.spl` exists. `bug_db.sdn` has said `fixed` since the landing; only this doc was stale.
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
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

## Ordinary transient-string retention: fixed

The runtime-wide owner fix keeps `RtCoreString` layout unchanged and uses its
existing reserved word to distinguish scope-owned ordinary strings from shared
short-cache and literal-intern strings. Scope teardown unregisters and frees an
ordinary string once regardless of how many transient containers alias it.
Promotion walks the reachable array/dict/enum/closure graph and clears transient
ownership, while strings created after pause remain process-persistent.

The core-C and Rust runtime twins implement the same boundary. The exact Rust
regression `transient_ordinary_string_is_reclaimed_and_aliases_free_once` passed
fresh on 2026-08-17 (1/1). Adjacent regressions cover reachable promotion,
unreachable sibling reclamation, short/literal shared-cache protection,
post-pause strings, and 128 repeated scopes returning to a fixed registry bound.
