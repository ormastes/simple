# bootstrap/stage3/simple SEGVs on both of its two commands (hello world)

- **Filed:** 2026-08-18
- **Severity:** HIGH — the tracked stage3 artifact is non-functional
- **Status:** OPEN (found while verifying an unrelated documented claim)
- **Artifact:** `bootstrap/stage3/simple`, 3,464,072 bytes, mtime 2026-08-11 22:10:05 UTC
- **Tracked in git:** yes (`git ls-files bootstrap/stage3` lists it)

## Symptom

The deployed stage3 bootstrap compiler segfaults on *both* commands it
advertises, on a three-line hello world. `--version` still answers, because it
never reaches the compile path.

```
$ ./bootstrap/stage3/simple --version
simple-bootstrap 1.0.0-beta

$ ./bootstrap/stage3/simple native-build /tmp/hello.spl -o /tmp/hello
Segmentation fault (core dumped)          # rc=139, after ~2.5s

$ ./bootstrap/stage3/simple compile /tmp/hello.spl --format=smf -o /tmp/hello.smf
Segmentation fault (core dumped)          # rc=139
```

`/tmp/hello.spl` in full:

```
fn main() -> i64:
    print "hi"
    0
```

This is not input-specific: a real target (`src/app/cli/lint_entry.spl`) SEGVs
identically and just as fast. The failure is in the binary, not the source.

## Why it matters

`bootstrap/stage3/simple` is the pure-Simple compiler the bootstrap chain hands
to stage 4. A stage3 that cannot compile hello world cannot produce a stage4
deploy, so the whole "default tooling = pure-Simple self-hosted binary" rule in
`CLAUDE.md` is currently unreachable from the tracked artifact. It also looks
green to every existing pre-push guard: they check tree structure, file counts,
`rt_*` symbol sets and C-runtime syntax, and none of them executes a stage
binary.

Same shape as the recently-recorded `6df4ed785c6` ("repo-wide parse block was a
STALE DEPLOYED SEED, not broken source"): the artifact is stale/broken, the
source is fine.

## Not fixed here

Rebuilding stage3 needs a bootstrap cycle, and as of this date `origin/main` is
separately unbuildable from half-landed Rust seed changes (duplicate
`INLINE_INT_BITS`/`fits_inline_int` in `runtime/src/value/core.rs`, an E0432 on
`module_globals_generation`, an E0599 on `f.as_ref()`), which another session
is repairing. Filed rather than attempted.

## Correction to a documented claim (the reason this was found)

`.claude/rules/commands.md` states:

> No pure-Simple binary can lint: `bootstrap/stage3/simple lint` is
> `unknown command` (exit 1).

The observation reproduces exactly —

```
$ ./bootstrap/stage3/simple lint
error: unknown command 'lint'          # rc=1
```

— but the conclusion drawn from it is wrong, in a way that has probably
discouraged work on a non-existent port. `bootstrap/stage3/simple` is built
from `src/app/cli/bootstrap_main.spl`, which is the **bootstrap** CLI and
deliberately exposes exactly two commands, `compile` and `native-build`
(dispatch at `src/app/cli/bootstrap_main.spl:459-492`; the `unknown command`
string is emitted at line 492 and exists nowhere else in a CLI path). It has no
`run`, `test`, `fmt` or `build` either. Asking it for `lint` is a category
error, not evidence of a missing implementation.

`lint` is already **fully pure Simple** and already wired into the full CLI:

- implementation: `src/app/cli/lint_entry.spl` -> `app.io.cli_lint_commands`
  (`run_lint_command` / `run_fmt_command` / `run_fix_command`); rule engine
  under `src/app/lint/main.spl` and `src/compiler/90.tools/lint/`
- dispatch, table form: `src/app/cli/dispatch/table.spl:113-118`
  (`CommandEntry(name: "lint", app_path: "src/app/cli/lint_entry.spl")`)
- dispatch, direct form: `src/app/cli/_CliMain/main_and_help.spl:349`
- bootstrap tool census already lists it:
  `src/app/cli/bootstrap_check.spl:357` — `["lint", "src/app/lint/main.spl"]`

Proof it runs as an ordinary Simple program, end to end, in ~6s:

```
$ bin/simple run src/app/cli/lint_entry.spl lint /tmp/tiny.spl
...
Lint passed: all files clean

$ bin/simple run src/app/cli/lint_entry.spl lint /tmp/dirty.spl
/tmp/dirty.spl:1:0: warning[RAW-RT-001]: application code must not declare raw
runtime intrinsic `rt_file_write_text` directly; use the std wrapper
Found 0 error(s), 1 warning(s), 0 auto-fix(es) available
```

The dirty fixture is the discrimination arm: the clean one emits no findings
line, so this is not a "the program printed something" tautology.

**So there is no lint port to do.** The real and only blocker is that no
full-CLI pure-Simple binary is currently deployed — which is the stage3/stage4
problem above, not a lint problem.

## Regression coverage

`scripts/check/check-pure-simple-lint-runnable.shs` (added with this record)
fences the corrected claim: it lints one clean and one dirty tiny fixture
through `src/app/cli/lint_entry.spl` and FAILs if the dirty fixture comes back
clean. `--selftest` additionally fails if the two fixtures produce identical
output, so an inert oracle cannot pass. Verdict is the last stdout line;
current result:

```
PASS - 2 fixture(s) linted, pure-Simple lint_entry.spl executed and its
findings discriminate (bin/simple)
```

Fixtures are deliberately 2 and 4 lines: lint cost is superlinear in file
content (measured table in `.claude/rules/commands.md`), and the guard never
batches files.

## Suggested follow-up

1. Rebuild and re-deploy stage3 once the seed builds again; re-run the two
   hello-world commands above as the acceptance check.
2. Consider an eighth pre-push guard in the family of
   `check-c-runtime-compiles-push.shs` — one that *executes* a tracked stage
   binary on a hello world — since no existing guard would have caught this.
3. Amend the `.claude/rules/commands.md` bullet quoted above; the observation is
   right, the inference is not.
