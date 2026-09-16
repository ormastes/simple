# Reported 20x bootstrap-env compile regression is NOT reproducible on the deployed seed

## Status

NOT REPRODUCED (2026-08-24, Lane T). The reported defect — a 20x wall / +73%
RSS regression caused by `SIMPLE_BOOTSTRAP=1` + `SIMPLE_BOOTSTRAP_STAGE4=1`
alone — did not appear in any of the six seed configurations measured below. The claim is
**UNKNOWN**, not refuted: the binary and invocation behind the original numbers
were never recorded and could not be recovered. Root cause therefore remains
open.

Area: bootstrap environment gating (`SIMPLE_BOOTSTRAP`, `SIMPLE_BOOTSTRAP_STAGE4`)
Guard: `scripts/check/check-bootstrap-env-cost-parity.shs`

## The claim

Lane M isolated, but did not root-cause, a regression compiling
`src/app/mcp/main.spl` (61-module closure) with the SAME binary, gate OFF on
both sides:

| config | MAXRSS | wall |
|---|---|---|
| plain env | 1,169,796 KB | 16.56 s |
| `SIMPLE_BOOTSTRAP=1` + `SIMPLE_BOOTSTRAP_STAGE4=1` | 2,026,216 KB | 343.19 s |

Recorded as limit (c) of the §27 row of
`doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md`.

**The numbers were never committed.** Neither the §27 table nor any bug record
in this worktree, nor Lane M's own worktree
(`/mnt/data/worktrees/goal-lane-m-memory-retention`), contains them, and no
recorded invocation or binary identity accompanies them.

## What was measured (Lane T, 2026-08-24)

Binary for every row: `bin/release/x86_64-unknown-linux-gnu/simple`,
60,650,360 bytes, mtime 2026-08-23 04:47 (the deployed Rust seed). Fresh
`--cache-dir` per run, so no run is a cache hit of another. Box load ~4,
`free -g` available 88-92 GB throughout. Exit status read directly into a
variable on the line after each invocation, never through a pipe.

Invocation shape taken from the real Stage-4 lane
(`scripts/check/check-stage4-selfhost-parse-memory-multifile.shs:234-243`):

```
$BIN native-build --target x86_64-unknown-linux-gnu --backend cranelift \
  --runtime-bundle core-c-bootstrap --source src/app/mcp --entry-closure \
  --threads 1 --mode dynload --cache-dir <fresh> \
  --entry src/app/mcp/main.spl -o <out>
```

| # | config | wall | MAXRSS | rc |
|---|---|---|---|---|
| a | plain env | 15.27 s | 137,656 KB | 1 |
| a' | plain env (repeat, + phase profile) | 15.45 s | 137,728 KB | 1 |
| c | `SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_STAGE4=1` | 16.17 s | 137,684 KB | 0 |
| c' | same (repeat, + phase profile) | 15.08 s | 137,692 KB | 0 |
| e | full Stage-3 env set (BOOTSTRAP, STAGE4, LOW_MEMORY, STREAMING_SURFACES, ARENA_DECLS, ENTRY_CLOSURE, PHASE_PROFILE) | 15.66 s | 137,684 KB | 0 |
| ob | plain env, `--mode one-binary` | 15.48 s | 137,684 KB | 1 |

Closure size is confirmed real, not a truncated build: config e reported
`Build complete: 59 compiled, 0 cached, 0 failed` / `4.2s compile + 11.2s link`.

**No configuration is more than 6% off any other. Nothing resembling 20x, and
RSS is flat at ~137 MB — 8.5x below the reported plain-env baseline.**

## Why the original numbers cannot be from this path

Three independent signals say the reported measurement came from a different
binary or invocation:

1. **RSS is off by 8.5x on the *plain* side** (137 MB measured vs 1,169,796 KB
   reported). Whatever Lane M ran held the whole closure in one process; the
   seed path spreads it across per-module workers.
2. **The seed never executes the `.spl` bootstrap gates.** Every
   `SIMPLE_BOOTSTRAP` / `SIMPLE_BOOTSTRAP_STAGE4` branch under
   `src/compiler/20.hir/**` and `src/compiler/80.driver/**` is Simple source.
   Runs a-e emitted **zero** `[BOOTSTRAP-PHASE]` lines with
   `SIMPLE_COMPILER_PHASE_PROFILE=1` set, proving `driver_aot_pipeline.spl`
   never ran. The seed has its own 19 Rust-side reads of `SIMPLE_BOOTSTRAP`,
   and those are what runs a-e actually exercised.
3. **The interpreted `.spl` route is far slower than the reported baseline.**
   `bin/simple run src/app/cli/native_build_main.spl <same args>` does reach the
   Simple driver (confirmed by `[bootstrap-error-count]` markers), at 2.4 GB
   RSS — but in **plain env** it reached only source index 2 of 59 after ~11
   minutes. It cannot be the source of a 16.56 s plain-env baseline. Killed;
   no numbers claimed from it.

Stage binaries were not an option: this worktree contains no `bootstrap/*/simple`
artifact, and per `.claude/rules/vcs.md` the tracked ones SEGV on both supported
commands anyway.

## A confound that must be controlled in any re-measurement

On `src/app/mcp/main.spl` the two sides **do not do the same work**. Plain env
aborts early:

```
error: semantic: cannot compile to standalone native binary:
80 function(s) contain constructs that require the interpreter
```

`src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs:867` reads
`if unresolved > 0 && std::env::var("SIMPLE_BOOTSTRAP").as_deref() != Ok("1")`
— bootstrap mode **suppresses** exactly this abort. So plain (rc=1) bails
before codegen while bootstrap (rc=0) runs to completion and emits a 672 KB
binary. Any plain-vs-bootstrap ratio on this entry is partly a work delta, not
pure environment overhead. Lane M's 16.56 s plain baseline is very likely such
a partial run, which would make the reported ratio an overstatement of unknown
size. This is the single most likely explanation for the reported 20x and
should be checked first if the configuration is ever recovered.

## Guard

`scripts/check/check-bootstrap-env-cost-parity.shs` pins the observable rather
than a mechanism (no mechanism was established, so encoding one would be
fiction). It compiles a synthetic 40-module closure twice with the same binary
— plain, then `SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_STAGE4=1` — and fails if the
bootstrap wall exceeds 4x the plain wall. The synthetic fixture is deliberate:
both sides complete with rc=0, so the work-asymmetry confound above cannot
contaminate the ratio.

Verdict convention matches the other guards: `PASS — <n> configuration(s)
timed, ...` exit 0 / `FAIL — ...` exit 1 / `ERROR — nothing was checked
(<reason>)` exit 2. A run that timed 0 configurations is ERROR; a fixture too
fast to discriminate (plain < 2 s) is ERROR, not a vacuous pass; a missing
verdict line must be read by the caller as FAIL. `--selftest` runs first
unconditionally and is fatal — 8 fixtures, including a replay of the reported
16.56 s -> 343.19 s shape that must FAIL, and zero/empty timings that must
ERROR.

Measured 2026-08-24:

```
selftest OK (8 fixtures)
plain:     10826ms (rc=0)
bootstrap: 10522ms (rc=0)
PASS — 2 configuration(s) timed, plain=10826ms bootstrap=10522ms, ratio=97 budget=400 (budget 4x)
```

## Still open / UNKNOWN

- **The originating binary and invocation.** Without them the 20x is neither
  confirmed nor refuted. Lane M must supply: binary path + size + mtime, the
  exact argv, and the env set — the evidence bar every other row in §27 meets.
- **Whether the reported ratio is a work delta** rather than env overhead (see
  the confound above). Untested, because it needs Lane M's configuration.
- **The interpreted self-host really is glacial** — ~11 min for 2 of 59 modules
  in plain env, 2.4 GB RSS. That is a genuine and separately actionable cost
  (it is the user's "why do compiles take so long" question), but it is *not*
  env-var-conditional and so is not this defect. Related, distinct, and already
  filed: `seed_per_call_env_rebuild_o_globals_regression_2026-08-21.md`.
- This guard covers the seed path only. It would not have caught a regression
  that lives exclusively in the `.spl` driver, because no runnable pure-Simple
  compiler exists in this worktree to exercise it.
