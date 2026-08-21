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

## Scope is wider than this record's title (2026-08-18)

Not stage3-only. Every git-tracked stage binary is dead on both of its
commands, and every one of them answers `--version` cleanly, which is
exactly why they look healthy:

| binary | compile | native-build | --version |
|---|---|---|---|
| `bootstrap/stage1/simple` | rc=139 | rc=139 | ok |
| `bootstrap/stage2/simple` | rc=139 | rc=139 | ok |
| `bootstrap/stage3/simple` | rc=139 | rc=139 | ok |
| `bootstrap/stage3/x86_64-unknown-linux-gnu/simple` | rc=139 | rc=139 | ok |

`bootstrap/stage1/simple` is git-tracked but ABSENT from the working
tree; it was materialised from HEAD to test, and crashes the same way.

12 invocations across 4 binaries, 8 crashed. Pinned by
`scripts/check/check-stage-binaries-runnable.shs`, which is honestly RED
and marked ADVISORY until a bootstrap redeploy lands.

Note this also means the recorded stage2/stage3 byte-identical
"bootstrap fixpoint" holds over binaries that do not work: the fixpoint
check compares artifacts to each other, never runs them.

## Re-confirmed 2026-08-21, with two findings the original record missed

Guard verdict, unchanged and honest:
`FAIL — 12 invocation(s) executed across 4 binary(ies), 8 crashed/failed`
(all four binaries, both commands, rc=139; `--version` ok on all four).

**1. The four "stages" are ONE blob copied four times.** All four tracked
paths hash identically:

    905ce03696a4726e...  3,464,072 bytes  bootstrap/stage1/simple
    905ce03696a4726e...  3,464,072 bytes  bootstrap/stage2/simple
    905ce03696a4726e...  3,464,072 bytes  bootstrap/stage3/simple
    905ce03696a4726e...  3,464,072 bytes  bootstrap/stage3/x86_64-unknown-linux-gnu/simple

A genuine 3-stage bootstrap CANNOT produce this: stage2==stage3 is the
fixpoint, but stage1 is compiled by the Rust seed and must differ. So the
"stage2/stage3 byte-identical fixpoint" recorded above is degenerate — it
is one artifact compared against copies of itself. Last commit to touch
these paths is `ae55a746719` ("fix(vcs): restore tree wiped by
6f86ff32a7d"); the restore evidently wrote a single blob into all four
slots. The 8 failures are therefore 2 distinct failures, not 8.

**2. The crash is in the compile pipeline, and any `fn` declaration
triggers it.** It is not a startup or CLI fault:

| input | result |
|---|---|
| `fun main():` + `print("hi")` | rc=1, clean diagnostic: `HIR lowering error ...: unresolved name: fun` |
| `fn main() -> i64:` + `0` | rc=139, **zero bytes of output** before the fault |
| `fn main():`, `fn` + `return 0`, `fn` + `val x = 1` | rc=139, zero output |

So `fun` is not a keyword in these binaries (`1.0.0-beta` — a stale era
relative to the current tree, where `fun` is the keyword) and reaches HIR
with a proper error, while the era-correct `fn` form faults before the
first log line. Reduced fixture: two lines, `fn main() -> i64:` / `0`.

**Repair requires a bootstrap redeploy that rewrites these four tracked
paths; there is no source-side fix.** The binaries are committed blobs
built from a compiler generation that no longer exists in the tree.

## 2026-08-21 resolution path (recipe NOT executed)

### Probe result: the pinned stage3 does NOT fix this

A pinned-snapshot `bin/simple build bootstrap` returned `Bootstrap VERIFIED`
on 2026-08-21, producing `build/bootstrap-pinned/stage3/simple`
(9,432,408 bytes, 2026-08-21 03:36). Probed on a 3-line hello world in a
private temp dir:

| invocation | rc |
|---|---|
| `--version` | 0 (`simple-bootstrap 1.0.0-RC`) |
| `compile hello.spl -o hw_c` | 1 (`error: bootstrap compile supports --format=smf only` — argument rejection, not a crash) |
| `compile hello.spl --format=smf -o hello.smf` | **139 (SEGV, core dumped)** |
| `native-build hello.spl -o hw_n` | **139 (SEGV, core dumped)** |

Both crashes stop at the same point, after
`[build] surface_freeze unknown/unknown step 1/6 complete`. This is the same
shape as the tracked-blob defect. **Conclusion: deploying this artifact would
NOT make the guard green — `check-stage-binaries-runnable.shs` would still
FAIL.** A VERIFIED three-stage bootstrap proves the three stages agree
byte-for-byte; it does not prove the produced binary can compile anything,
because every stage is driven by the *seed*, not by a stage output. The
deploy recipe below is therefore recorded but **blocked**: do not run it until
a pinned stage3 probes rc=0 on both commands.

### Deploy recipe (for when a stage3 probes clean)

Replacements, all from the same pinned run:

| tracked path | replaced by |
|---|---|
| `bootstrap/stage1/simple` | `build/bootstrap-pinned/stage3/simple` |
| `bootstrap/stage2/simple` | `build/bootstrap-pinned/stage3/simple` |
| `bootstrap/stage3/simple` | `build/bootstrap-pinned/stage3/simple` |
| `bootstrap/stage3/x86_64-unknown-linux-gnu/simple` | `build/bootstrap-pinned/stage3/simple` |

All four get the *same* byte-identical stage3: a VERIFIED run means stage1 ==
stage2 == stage3, so shipping the fixpoint binary in every slot is exactly
what the stages are supposed to contain.

`cp .new` + `mv` is mandatory — a direct `cp` over a binary that any live
process has mapped fails with `Text file busy`:

```sh
SRC=build/bootstrap-pinned/stage3/simple
for D in bootstrap/stage1 bootstrap/stage2 bootstrap/stage3 \
         bootstrap/stage3/x86_64-unknown-linux-gnu; do
  cp "$SRC" "$D/simple.new"
  chmod +x "$D/simple.new"
  mv -f "$D/simple.new" "$D/simple"
done
```

Post-deploy guard (must print PASS, exit 0, before any commit or push):

```sh
sh scripts/check/check-stage-binaries-runnable.shs
```

Expected on success:
`PASS — 8 invocation(s) executed across 4 binary(ies), 0 crashes`.
Anything else means the deploy did not fix the defect — revert the four
blobs (`git checkout -- bootstrap/`) rather than committing. Promote the
guard from ADVISORY to MANDATORY in `.claude/rules/vcs.md` only after that
PASS is observed.
