# Perf Agent - Performance Regressions and Cost Bugs

**Use when:** Something got slower, a build/lint/test exceeds its budget, a hot
path needs a cost model, or a perf gate went red.
**Related:** `debug.md` (correctness first), `mem.md` (RSS/heap), `build.md`.

## Rule zero: a number without a binary identity is not a measurement

`bin/simple` is a symlink that other sessions replace mid-session. Record what
you actually ran, every time, or the timing is unattributable:

```bash
readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"
bin/simple --version 2>&1 | head -2     # says outright if it is the Rust seed
```

Also record: host load and concurrent `simple` processes. This box is shared;
figures taken at load 33-55 with 20+ concurrent compilers are an envelope, not
a datum. State which you have.

## Order of work

1. **Reproduce with a number.** No number, no bug. Wall clock AND the unit that
   moved (per file, per declaration, per request).
2. **Bisect the input, not the code, first.** Cost usually tracks a property of
   the input. Halve the file/case set until the cost halves — if it does not,
   the term is superlinear and that is the finding.
3. **Only then read code.** A profile beats a guess, but see the profiling
   caveat below before promising one.
4. **Pin it.** A fix with no gate regresses. Land a budget check.

## Profiling on this host is restricted — do not promise a flame graph

`ptrace_scope=1` and `perf_event_paranoid=4` block attach-based profiling.
Verify before planning around it:

```bash
cat /proc/sys/kernel/yama/ptrace_scope /proc/sys/kernel/perf_event_paranoid
```

What works without attach: the compiler's own phase profile, coarse timing
bisection, and `/proc/<pid>/stat` sampling (utime/stime deltas prove whether a
process is computing or sleeping — a process at 0.3% CPU in
`hrtimer_nanosleep` is waiting, not working, and that distinction has misled
sessions here).

```bash
# CPU actually advancing? sample utime/stime, do not trust a single top reading
for i in 1 2 3; do awk '{print "utime="$14" stime="$15}' /proc/<pid>/stat; sleep 20; done
cat /proc/<pid>/wchan; echo          # where it is blocked, if it is
```

## Compiler phase profile (no attach needed)

```bash
SIMPLE_COMPILER_PHASE_PROFILE=1 \
SIMPLE_COMPILER_PHASE_PROFILE_FILE=/tmp/phase.events  <compiler invocation>
```

Emits `schema=simple.compiler.mem_snapshot.v1` rows carrying `phase=`,
`heap_live_bytes`, `heap_peak_bytes`, `rss_kib`, `hwm_kib` per phase — the
cheapest way to attribute cost to a compiler phase.

**Cost warning, measured 2026-09-04.** `SIMPLE_COMPILER_PHASE_PROFILE=1` also
turns on the `[mir-lower]` trace (`mir_lower_trace_enabled()`, gated on
`SIMPLE_COMPILER_TRACE` / `SIMPLE_COMPILER_PHASE_PROFILE` / `SIMPLE_BOOTSTRAP_DIAG`).
On a Stage-3 build that produced **9,955,950 bytes** of stderr, and the
native-build entry then dropped 9,943,950 of them **from the middle**, taking
the actual `error:` lines with it. Turning this on can therefore destroy the
diagnostic you turned it on for. When you need the error, not the profile,
leave it OFF and read the separately-saved full stderr at
`<output>/stage3/<triple>/stage3-tmp/native-build-stderr-<pid>.log`.

## Known cost models (re-measure before trusting; dated)

- **Lint** is ~12s fixed startup, then a per-declaration cost driven by
  declaration CONTENT, not count. Declaration count scales roughly linearly;
  content complexity is superlinear in the file. Do not "fix" a slow lint by
  splitting a file into more functions — measured flat-to-falling per-decl cost
  from 15 -> 90 decls. Do not batch files: 2 files exceeded 600s vs 119s for 1.
  Numbers in `.claude/rules/commands.md` predate the 2026-08-18 seed redeploy
  and MUST be re-measured before use.
- **Bootstrap self-host stages run at 2 threads** by design ("self-host jobs: 2")
  and Stage 3's resume lane pins `--threads 1` unless
  `SIMPLE_NATIVE_BUILD_THREADS` is set. A Stage-3 stage at ~100% of ONE core is
  expected, not a hang — confirm with a utime delta before calling it stuck.
  `--jobs=full` covers the parallel stages; Stage-3 resume rejects it outright.

## Gates: use the existing one before writing a new one

34 perf/memory checks already exist under `scripts/check/`. Look first:

```bash
ls scripts/check/ | grep -iE 'perf|memory|budget|regress'
sh scripts/check/check-perf-regression-tests.shs      # advisory in the push tier
sh scripts/check/check-lint-cost-budget.shs           # fail-closed, --selftest
```

A new gate must follow the house convention or it is not trustworthy:
verdict is the **last line of stdout**; `PASS — <n> ... checked` with n > 0,
`FAIL` exit 1, `ERROR — nothing was checked` exit 2; a run that measured
nothing is ERROR, never a pass; `--selftest` runs first and is fatal. **Read the
subject command's exit status directly into a variable on the next line, never
through a pipe** — a pipeline's `$?` is `tail`/`grep`'s status and has produced
false greens in this repo.

## Reporting

Report the measurement, the envelope (load, concurrency, binary identity), and
the unit. If you did not fix it in the same change, record a concrete bug or
todo — CLAUDE.md forbids moving past a meaningful perf regression silently.
Metrics belong in `doc/10_metrics/`, dated.
