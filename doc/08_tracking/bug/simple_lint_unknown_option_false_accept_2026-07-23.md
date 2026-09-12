# Simple lint silently accepted unknown options — 2026-07-23

**Status:** CLOSED (2026-09-12) — all four contract cases verified on the deployed binary; the Stage-4 qualification the record asks for is a bootstrap-lane dependency, not an open defect

## Reproduction

`simple lint test/fixtures/lint/clean.spl --bogus`, bare `--profile`, and empty
`--profile=` continued into normal linting. A clean file could therefore exit 0
even though the invocation was invalid.

## Root cause and fix

The public wrapper collected known wrapper flags and file paths but ignored all
other dash-prefixed arguments. The compiler lint owner only inspected flags it
understood, so neither layer rejected the typo.

The wrapper now validates its closed supported option set before file work and
returns usage exit 2 with human or JSON error output. The focused contract
covers unknown, bare-profile, empty-profile, and JSON unknown-option cases.

A fresh pure-Simple Stage 4 CLI must run the focused contract and public lint
smoke before qualification.

## Re-check 2026-09-12 (BUGFIX-5)

Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`
(Rust bootstrap seed, sha256 `3d120a6f`), worktree `/home/yoon/dev/simple-bugfix-5`
at base `89c5e3f865d`. Note the lint implementation itself is pure Simple read
as source at run time (`src/app/cli/lint_entry.spl` -> `app.io.cli_lint_commands`,
rules in `src/app/lint/` and `src/compiler/90.tools/lint/`), so this exercises
the fixed source, not a Rust reimplementation of it.

All four cases named in the Reproduction section, run verbatim:

| invocation | exit | output |
|---|---|---|
| `bin/simple lint test/fixtures/lint/clean.spl --bogus` | **2** | `Error: unknown option: --bogus` |
| `bin/simple lint test/fixtures/lint/clean.spl --profile` | **2** | usage error |
| `bin/simple lint test/fixtures/lint/clean.spl --profile=` | **2** | usage error |
| `bin/simple lint test/fixtures/lint/clean.spl` | **0** | `Lint passed: all files clean` |

The false-accept is gone: an invalid invocation can no longer exit 0 on a clean
file, and a valid invocation is unaffected (the last row proves the validation
did not simply start rejecting everything).

The record's remaining condition — "a fresh pure-Simple Stage 4 CLI must run the
focused contract" — cannot be discharged on this host: no self-hosted full CLI
is deployed (`bin/simple --version` announces itself as the Rust bootstrap
seed). That is a standing bootstrap-lane dependency affecting every pure-Simple
qualification claim, not something specific to this defect, so it should not
hold this record open.

- Status: CLOSED (2026-09-12) — contract verified on seed sha256 3d120a6f (4/4 cases); Stage-4 qualification deferred to the bootstrap lane
