# Seed ↔ stage-2 differential corpus gate

Robustness item 12b. Driver: `scripts/check/check-seed-stage2-differential.shs`.
Status: **advisory, not wired** into any hook or CI lane (see "Why it is not wired").

## What it prevents

Nearly every bootstrap blocker of October 2026 was a program the Rust seed runs one way and the
pure-Simple stage-2 compiler rejects or compiles differently: bare variants read as bindings,
explicit generic arguments dropped (`E-MONO-032` on `f<T>(...)`), `3 == nil` being true,
`mod.spl` vs `__init__.spl`, `# Re-exported from` comment hints, ignored match guards, missing
builtin lowerings. Each was found one at a time, 40 minutes into a phase-3 build. The gate keeps
one small program per divergence class and reports, per program, whether the two compilers still
agree.

## How it reports

For every case it runs

- **A** the seed interpreter, `<seed> run <case>/main.spl` — the oracle;
- **B** the stage-2 compiler, `<stage2> native-build --backend llvm` and `--backend cranelift`,
  then the produced executable;

and compares **exit code + stdout**. One row per (case, lane):

| lane | compares | verdicts |
|---|---|---|
| `seed` | seed vs the expectation written in the case header | SAME / DIFF / NOTRUN |
| `llvm`, `cranelift` | stage-2 vs the seed | SAME / DIFF / NOTRUN |

A *refusal* is: the seed exits non-zero with empty stdout; stage-2 `native-build` fails. Both
refusing is SAME. `NOTRUN` (timeout, backend not built into this stage-2, no `main.spl`) is never
counted as agreement. The `seed` lane exists because the oracle is sometimes the wrong side
(`diff_nil_eq_int`: the seed itself prints `three=true`).

The verdict is the last stdout line:

```
PASS  — <n> comparison(s) across <c> case(s) [...]: <s> SAME, <d> baselined DIFF, <k> baselined NOTRUN, 0 new, 0 stale   exit 0
FAIL  — ... new DIFF: <case>:<lane>; unbaselined NOTRUN: ...; stale baseline: ...; baseline class changed: ...        exit 1
ERROR — nothing was checked (<reason>)                                                                                exit 2
```

`ERROR` covers: no `--stage2`, a missing or non-executable seed or stage-2, an empty corpus, a
malformed baseline row, a failed selftest, and a run in which no row was actually compared.

## Running it

```sh
# Windows (Git Bash), frozen diagnostic stage-2:
. ~/.simple/toolchains/activation/windows-llvm-23.1.1.shs
export SIMPLE_WINDOWS_ABI=msvc SIMPLE_LINKER_FLAVOR=msvc CC="$LLVM_SYS_231_PREFIX/bin/clang-cl.exe"
sh scripts/check/check-seed-stage2-differential.shs \
    --stage2 <dir>/simple.exe --seed <seed>/simple.exe --target x86_64-pc-windows-msvc

# Linux / macOS: toolchain env from scripts/setup/llvm-toolchain-env.shs, no --target needed.
sh scripts/check/check-seed-stage2-differential.shs --stage2 <path> --seed <path>

sh scripts/check/check-seed-stage2-differential.shs --selftest       # no compiler needed
sh scripts/check/check-seed-stage2-differential.shs --stage2 <p> diff_match_guard   # one case
```

Options: `--runtime <dir>` (default `<stage2 dir>/stage2-runtime-authority`), `--backends
llvm,cranelift`, `--jobs <n>` (parallel stage-2 builds, default 2), `--threads`, `--timeout`,
`--work`, `--baseline`, `--corpus`. `BOOT=` (empty) unsets `SIMPLE_BOOTSTRAP`; `KEEP_WORK=1` keeps
per-build caches and executables. Each stage-2 build uses its own cache directory, deleted after
the build — a shared cache would let one case's objects answer for another.

Cost: the seed lane is seconds per case; one stage-2 native-build is 1.5–4 minutes, so the full
corpus (28 cases × 2 backends) is about 1.5–2 hours at `--jobs 2` on the Windows host.

## Level switch

There is no compiler-side switch: this is an out-of-tree gate and adds nothing to a build. To skip
it, do not run it. To narrow it: name cases on the command line, or `--backends llvm`. A run
restricted by case names or backends does not judge baseline rows outside that restriction.
`--no-selftest` skips only the fatal selftest (the acceptance spec uses it after running
`--selftest` once); it does not relax any comparison.

## The baseline (shrink-only)

`scripts/check/seed_stage2_differential_baseline.txt`, one row per known divergence:

```
<case> <seed|llvm|cranelift> <DIFF|NOTRUN>  # why
```

- a `DIFF` / `NOTRUN` row **not** in the baseline fails (new divergence);
- a baselined row that is now `SAME` fails as **stale** — delete the row in the fixing change;
- a row whose class changed (`NOTRUN` ↔ `DIFF`), or whose case no longer exists, fails;
- `--generate-baseline` rewrites the file from the current run. Reviewed updates only: read the
  table first; regenerating to turn a FAIL green hides a new divergence.

A baseline describes **one stage-2 binary**. The shipped file was produced with the frozen
diagnostic stage-2 named in its header; a newer stage-2 is expected to make rows stale, which is
the signal to delete them.


### Re-baselining against another stage-2 (one command)

Add `--generate-baseline` to the normal invocation; the file header records the binary's sha256:

```sh
sh scripts/check/check-seed-stage2-differential.shs --stage2 <new stage2>/simple.exe \
    --seed <seed>/simple.exe --target x86_64-pc-windows-msvc --generate-baseline
git diff scripts/check/seed_stage2_differential_baseline.txt    # every removed row = a divergence closed
```

Use `--baseline <file>` to keep a second binary's baseline beside the shipped one instead of
replacing it. Shipped state (frozen diagnostic stage-2 `5d97a3dc…`, 2026-10-10, Windows MSVC):
84 comparisons, 35 SAME, 49 DIFF (5 on the `seed` lane, 21 `llvm`, 23 `cranelift`), 0 NOTRUN.

## Adding a case

1. `test/fixtures/bootstrap/stage2_micro/diff_<class>/main.spl` — this is the stage-2
   micro-program ladder's directory and header format (its `run.shs` is the stage-2-only runner):

   ```
   # Differential case: <one line>.
   # Class: <bug record / plan id>.
   # Expected stdout:
   #   <exact line>
   ```

   or `# Expected: reject` for a program both compilers must refuse.
2. Sibling modules import as `test.fixtures.bootstrap.stage2_micro.<case>.<module>`.
3. Keep it to one divergence class, deterministic, no I/O beyond `print`.
4. Run the one case; if it diverges for a known, filed reason add the baseline row with the bug
   id in the comment.

The expectation in the header is the language's intended answer, not "whatever the seed prints";
where the seed disagrees, the `seed` lane says so.

## Why it is not wired

A manifest row needs a fixed command. This gate needs an explicitly chosen stage-2 binary with
its runtime authority and a native linker toolchain, and about two hours of stage-2 builds; no
hook and no hosted runner has an admitted stage-2. It is therefore listed in
`scripts/check/guard_wiring_optout.txt` with that reason. Promotion path: once a bootstrap lane
publishes a stage-2, add a `bootstrap`-tier `push_blocking: false` row that passes that lane's
stage-2 to `--stage2`, and promote to blocking when the baseline is empty.

## Known limits

- Equal output is not proof of equal semantics; the corpus only covers the classes it lists.
- Seed `refuse` is inferred from "non-zero exit and empty stdout"; a program that prints and then
  fails is treated as having run.
- `SIMPLE_BOOTSTRAP=1` (the default, as in `run.shs`) skips MIR lowering for non-entry modules,
  so multi-module cases exercise resolution and linking more than non-entry codegen.
- RBH T03, T05–T07, T10–T15, T17, T18 are not expressible as a single run-and-compare program
  (async, GPU parser, CLI verdicts, scaling, known-answer vectors) and are not in the corpus.
- The baseline is specific to one stage-2 binary and one host triple.
- The selftest is process-spawn bound: seconds on Linux, about three minutes on a loaded Windows
  host.

## Acceptance

`test/03_system/compiler/seed_stage2_differential_acceptance_spec.spl` drives the real driver
with the fake compilers in `test/fixtures/bootstrap/seed_stage2_differential_selfcheck/`:
agreement, stdout divergence, stage-2 refusal, exit-code divergence, both-refuse, baselined
divergence, stale baseline, NOTRUN, missing compilers, empty corpus, and corpus/baseline shape.
