# Hardcoded CLI option census — Phase C / C4 migration report (2026-08-18)

**Purpose.** Phase C (startup_perf_plan_2026-08-17.md, WP-19c) moves CLI
options to SCI route data (`cli_option_route.spl` records). C4's help /
completion generator (`src/lib/nogc_sync_mut/composition/cli_help_gen.spl`)
derives help + completions from that data. This census records which option
spellings are still HARDCODED as string literals in `src/app/cli/**` and are
therefore candidates for route migration.

**Method.** `/usr/bin/grep -roE '"--[a-z][a-z0-9-]*"'` (and `'"-[a-zA-Z]"'`
for short flags) over `src/app/cli --include=*.spl`, 2026-08-18, worktree
lane-aspect-dynload.

**ALL COUNTS ARE UPPER BOUNDS.** Hits were NOT individually adjudicated; a
literal like `"--json"` may be a doc string, an example, an argv literal
passed to a child process, or a real hand-parsed option. These are migration
CANDIDATES, never a defect count.

## Long-option literals (`"--<name>"`)

- Distinct spellings: **86** (upper bound)
- Total literal occurrences: **278** (upper bound)
- Files containing at least one: **36** of the `.spl` files under `src/app/cli`

Top spellings by occurrence (upper bound):
`--help` 17, `--format` 15, `--json` 11, `--output` 9, `--backend` 9,
`--log-mode` 8, `--entry` 8, `--progress` 7, `--verbose` 6, `--timeout` 6,
`--start-line` 6, `--end-line` 6, `--surface` 5, `--source` 5, `--quiet` 5,
`--no-progress` 5, `--llm` 5, `--human` 5, `--dots` 5, `--count` 5,
`--target` 4, `--runtime-bundle` 4, `--requester` 4, `--query` 4, `--mode` 4
(remaining 61 spellings occur 1-3 times each).

## Short-flag literals (`"-x"`)

Upper bound occurrences: `-h` 17, `-o` 13, `-c` 8, `-v` 4, `-r` 3, `-n` 3,
`-E` 3, `-m` 2, `-l` 2, `-s`/`-p`/`-j` 1 each. `-h`/`--help` and
`-V`/`--version` are RESERVED core spellings (`cli_spelling_reserved_v1`)
and stay hardcoded by design — they are excluded from migration scope.

## Route-driven today

Zero product options are yet registered through
`SimpleCliOptionRouteTableV1`; the generator and route layer exist, the
migration itself is the remaining Phase C work.
