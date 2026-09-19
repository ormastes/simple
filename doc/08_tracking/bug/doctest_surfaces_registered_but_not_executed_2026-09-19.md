# BUG: the markdown and comment doctest surfaces are wired but effectively execute nothing

- **id:** doctest_surfaces_registered_but_not_executed_2026-09-19
- **status:** OPEN — measured, not fixed
- **severity:** P2 — a whole declared test surface is inert; no wrong answers, but 1,632 markdown examples and 89 comment examples are unverified while appearing to be "part of the maintained test surface"
- **found:** 2026-09-19, while running the four test surfaces end to end

README.md states: *"Executable examples are part of the maintained test
surface."* Measured below, almost none of them are.

## Surface 1 — markdown doctests: in scope, not discovered

`config/sdoctest.sdn` puts these in scope, minus an ignore list
(`doc/11_archive`, `09_report`, `06_spec`, `05_design`, `01_research`,
`03_plan`, `10_metrics`, `08_tracking`):

| source | files with a `simple`/`spl` fence | fences |
|---|---|---|
| `README.md` | 1 | 13 |
| `doc/` (after ignores) | 267 | 1,512 |
| `examples/` | 25 | 88 |
| `.claude/skills/` | 6 | 19 |
| **total** | **299** | **1,632** |

The full test manifest registered **`sdoctest_count=1`**, and that single entry
is `test/01_unit/app/simple_lab/fixtures/hello_sdoctest.md` — a fixture which is
**not in the configured scope at all**.

### Mechanism

`discover_sdoctest_files` (`src/lib/nogc_sync_mut/test_runner/sdoctest/discovery.spl:16`)
short-circuits on a CLI path:

```
fn discover_sdoctest_files(config: SdoctestConfig, cli_path: text) -> [text]:
    # If CLI path override is given, use it directly
    if cli_path != "":
        ...
        return []
    # Walk all configured sources
```

So any invocation that names a path — `bin/simple test test/01_unit`, or any
scoped run — never walks `config.sources`. It finds only markdown that happens
to live under the named path, which is why a fixture under `test/01_unit` is the
one thing registered.

This is not a wrong answer, and arguably the override is intended. What is
defective is the *net effect*: the configured markdown corpus runs only when the
path argument happens to point at it, so a normal `bin/simple test <dir>` run
reports success while executing none of it.

### It is not vacuous — pointing at the corpus finds a real defect

```
bin/simple test README.md
  SDoctest Results: 19 total, 18 passed, 1 failed, 0 skipped, 0 errors
```

18 of those 19 blocks had never been executed by any scoped run. The single
failure is a genuine documentation/implementation mismatch, filed separately as
`readme_arrow_match_arm_syntax_does_not_parse_2026-09-19` — the README documents
`| Pattern -> expr` match arms as "preferred" and the parser rejects them.

That is the argument for fixing this: the first time the surface was actually
run, it caught something.

## Surface 2 — comment doctests: opt-in, and extract zero examples

Comment doctests are gated behind `SIMPLE_SDOCTEST_SPL=1`, with the reason
stated in `discovery.spl:24`:

> Source-comment doctests (.spl) are OPT-IN: SIMPLE_SDOCTEST_SPL=1.
> 138 bodies in owned source have never executed; enabling them tree-wide by
> default would turn a silent gap into a loud red.

Census of owned source (`src/**/*.spl`, comment-embedded `simple`/`spl`/
`sdoctest` fences): **89 fences across 36 files**.

With the flag **on**, files that demonstrably contain such fences still execute
nothing:

```
SIMPLE_SDOCTEST_SPL=1 bin/simple test src/lib/nogc_sync_mut/concurrent/channel.spl
  VERDICT: outcome=ERROR declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=zero-examples

SIMPLE_SDOCTEST_SPL=1 bin/simple test src/lib/gc_async_mut/platform/mod.spl
  VERDICT: outcome=ERROR declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=zero-examples
```

Two independent files, both carrying real fences, both `executed=0`. So the
opt-in flag is not the whole gate: even opted in, the comment extractor yields
no examples. The `reason=zero-examples` verdict is at least honest — it reports
`ERROR`, not a pass — but nothing routinely runs it, so nobody sees it.

## What this is NOT

`check-doctest-registration-coverage.shs` reports `FAIL — 272358
unregistered-or-undecidable fence(s)`. That number is **not** 272k broken tests
and should not be quoted as one: its dominant cause is
`md-file-not-in-sdoctest-source-scope` for files like `.claude/plan.md` and
`.codex/commands/coding.md`, which the config deliberately excludes. The guard
labels its own figure an "UPPER BOUND: raw block rows, not adjudicated defects".
The real, in-scope gap is the 1,632 + 89 above.

## Suggested order for whoever takes this

1. Decide whether a path-scoped run should still walk `config.sources` for
   markdown. If yes, that is a small change in `discover_sdoctest_files` and it
   immediately puts 1,632 fences under test — expect an initial red.
2. Fix the comment extractor's `zero-examples` result before flipping
   `SIMPLE_SDOCTEST_SPL` on by default; the flag currently hides a lane that
   would not run anyway.
3. Land `readme_arrow_match_arm_syntax_does_not_parse_2026-09-19` first or
   together, since it is the one known red in the markdown corpus.

## Related

- `readme_arrow_match_arm_syntax_does_not_parse_2026-09-19` — the defect the md
  surface caught the first time it was actually run.
- `rt_file_stat_returns_size_on_interpret_lane_2026-09-19` — same session, also
  found by exercising something nothing routinely exercises.
