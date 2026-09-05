# Stale deployed binaries reject current-language source — sspec-maintain scorer unrunnable on this Mac

Date: 2026-09-05. Found while trying to run `sspec-maintain scan` (modern sspec
documentization score) for the all-specs-to-80 goal.

## Symptom

Every binary available on this host failed before the scorer could run:

| Binary | Date | Failure |
|---|---|---|
| `bin/simple` → `bin/release/aarch64-apple-darwin-macho/simple` (bootstrap CLI, `simple-bootstrap 1.0.0-beta`) | stale | parse error: `val x = unsafe(...):` block-expr in `src/lib/nogc_sync_mut/io/file_ops.spl:134` — "unexpected token in expression: `:`" |
| `bin/release/aarch64-apple-darwin-macho/simple_seed` (Rust seed) | **Jul 25 13:12** | parse error: unparenthesized multi-line boolean chain — "Unexpected token: expected expression, found Indent" (first hit `src/lib/common/perf/execution_metrics.spl:365`, then `src/app/sspec_maintain/source_facts.spl`) |
| `bin/release/aarch64-apple-darwin/simple` (also a seed build) | Jul 25 14:15 | same class |
| `bin/local/phase2-aarch64-apple-darwin/simple` (`simple-bootstrap 1.0.0-rc.1`, built today by a parallel lane) | Sep 5 11:51 | parses current source, but AOT `compile error ... <invalid-heap>` on a hello world + HIR `unresolved type: Id` on generic struct params — WIP/broken lane binary, not usable |
| `.bak-2026-07-25-cli` backups | Jul 25 | also seed builds with the same parser staleness |

## Root cause

**Not a parser-logic defect.** Both toolchains' SOURCE already accept the
"offending" constructs:

- Unparenthesized multi-line boolean chains: fixed 2026-08-04/08-11 in the
  seed parser (guarded by `src/compiler_rust/parser/src/rejoined_continuation_test.rs`
  — `rejoined_nested_continuation_parses`, `observation_matches_shape_parses`).
  The pure-Simple compiler accepts them too (current `src/**` relies on them
  throughout, e.g. `execution_metrics.spl`).
- The deployed binaries simply predate the fixes: seed built **Jul 25**, six
  weeks of language evolution ago. `@always_inline` (landed Aug 26) and the
  `unsafe(...)` block expression likewise postdate them.

Secondary aggravator: this Mac's disk was 100% full (301 MiB free), which
surfaced as `ENOSPC` on tool outputs before anything else. Freed 60+ GiB by
removing 15 stale `/tmp` and `~/Library/Caches/simple/worktrees` git worktrees
(from Sep 3-4 lanes).

## Fix

Rebuild the seed from current source (running at time of writing):
`cd src/compiler_rust && cargo build --profile bootstrap -p simple-driver -p simple-native-all`.
Longer term: the sanctioned redeploy (`scripts/bootstrap/bootstrap-from-scratch.sh
--pure-simple --deploy`) so `bin/simple` is a current self-hosted binary — the
beta-era bootstrap binary currently pointed at `bin/simple` cannot parse the
current stdlib at all.

## Directive recorded on request (user, 2026-09-05)

**Do not add parentheses merely to make a multi-line boolean chain parse.**
Unparenthesized continuation after a trailing `and`/`or` is the intended,
readable form and is fully supported by current toolchain source. Adding `(...)`
wrappers around every continuation makes the code LESS readable and must not be
normalized into specs or product code; parentheses are for precedence grouping
only. (A temporary paren-rewrite of `source_facts.spl` made during diagnosis was
reverted — `git checkout` — for exactly this reason.) `.claude/rules/language.md`
updated accordingly.
