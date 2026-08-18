# native-build: interpreted worker carries a fixed ~2.4 GB RSS floor before it compiles anything

- **Filed:** 2026-08-18
- **Status:** OPEN — measured, not fixed
- **Severity:** HIGH — this is the mechanism by which `earlyoom` reaps the bootstrap
- **Area:** `src/app/cli/native_build_worker.spl`, `src/app/io/_CliCompile/compile_targets.spl`,
  seed interpreter module loading

## What was measured

`bin/simple native-build` does not compile in-process. It **spawns**
`bin/simple run src/app/cli/native_build_worker.spl <entry>` — i.e. the pure-Simple
compiler is executed **interpreted** by the Rust seed. All of the memory below is
that worker process.

Binary under test: `bin/release/x86_64-unknown-linux-gnu/simple` (`bin/simple` symlink),
host load ~100 with ~20 concurrent `simple` processes.

| case | what it does | peak RSS | method |
|---|---|---|---|
| `simple run hello.spl` | interpreter, trivial closure | **0.04 GB** | `/usr/bin/time -v` MaxRSS |
| `simple run src/app/cli/native_build_worker.spl` (**no args**) | loads the compiler closure, **compiles nothing, emits zero diagnostics** | **2.37 GB** | `/usr/bin/time -v` MaxRSS |
| `native-build t2.spl` (2-line entry, `source_closure 1/1`, 0 warnings) | full build of one trivial file | **2.35 GB** | 1 Hz `ps rss` sampling of the worker pid |
| `native-build` of a syntactically INVALID 2-line file (dies at HIR with `unresolved name: fun`) | never reaches lowering | **2.53 GB** | 1 Hz `ps rss` sampling |
| other lanes' concurrent `native_build_worker` processes | unrelated builds | **2.47–2.49 GB each** | `ps -eo rss` |

## The amplification factor

`strace -f -e trace=openat` on the **no-argument** worker run (the 2.37 GB case
above — it compiles nothing) shows the interpreter opening:

- **1262 unique `.spl` files**, totalling **20.6 MB of source**
- **2371 total `.spl` opens** — 1.88x redundant re-opens of the same files

**20.6 MB of source -> 2.37 GB resident is a ~115x in-memory amplification**,
paid before the first line of target code is looked at. For scale, the whole
owned `.spl` corpus (`src/compiler` + `src/lib` + `src/app`) is 12,126 files /
84.3 MB, so the worker is materialising about a quarter of the tree just to
start.

## Which hypothesis this supports

The brief posed two: RSS scales with **diagnostic count**, or with **source-closure size**.

**Diagnostic count is REFUTED, decisively.** The no-argument worker run compiles
nothing and produces zero diagnostics, and still reaches 2.37 GB — 100% of the
2.35 GB that a complete trivial build costs. Independently, on the Rust-seed side
the `warning: unresolved call ...` lines are emitted by bare `eprintln!` at
`src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs:651,662,675`
with only an `unresolved_count: &mut usize` retained — the text is streamed, never
accumulated. The R9 diagnostic cap (`8ea9c62d05b8`) is therefore not the missing
piece here, and extending it to warnings would recover nothing.

**Source-closure size is supported, but not the closure you would expect.** The
2.4 GB is not the *target's* closure — `t2.spl` reports `source_closure 1/1` and
costs the same as everything else. It is the **compiler's own** source closure,
materialised by the seed interpreter when the worker's three imports transitively
pull in the driver. `native_build_worker.spl` is 27 lines with three `use` lines;
that is enough to cost 2.37 GB.

So: **~2.4 GB is a fixed per-invocation floor, paid before any user code is seen,
and it is paid by every concurrent native-build on the box.**

## Why this kills the bootstrap

`earlyoom` on this host fires at 10% free with zero swap and reaps the largest
process. It has killed the bootstrap three times. With ~15 lanes each holding a
2.4 GB floor, the box is already near the edge before any single build's
variable cost is added.

## Not verified

- The 20 GB single-process peak reported for the bootstrap admission-planner build
  was **not reproduced here**, and the obvious explanation for the gap was
  **tested and refuted**. My direct
  `native-build src/app/cli/bootstrap_reason_planner.spl` peaked at 2.48 GB. I
  then replicated the bootstrap's exact argv from
  `scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs:152` —
  `native-build --source <root>/src/app/cli --source <root>/src/lib --entry ... -o ...`
  — on the hypothesis that passing directory roots expands the compiled closure.
  It does not: that run reports `source_closure 6/6`, `load_sources 7/7`. `--source`
  adds *search roots*, it does not enlist directories. **So the 20 GB is still
  unexplained and no measurement in this report reproduces it.** The remaining
  untested difference is the bootstrap's environment (`SIMPLE_BOOTSTRAP=1`,
  `SIMPLE_RUNTIME_PATH`, and the `env -i` sanitised env), which I did not
  replicate. That is the next thing to try.
- Measurement caveat worth recording: the `--source ... --entry` form and the bare
  `native-build <entry>` form do **not** take the same process shape. The bare form
  spawns the `native_build_worker` child; the `--source/--entry` form did not show a
  worker child while under observation. Any RSS sampler that greps only for
  `native_build_worker` silently measures nothing on the bootstrap's argv — my first
  sampler did exactly that and reported another run's numbers. Sample the whole
  process tree.
- A second sampler bug worth recording because it produced a plausible-looking
  wrong answer: summing `VmHWM` over `pstree -p` output double-counts, because
  `pstree -p` lists **threads** as well as processes and every thread of a process
  reports that process's full `VmHWM`. That sampler reported a 12.22 GB tree total
  — tantalisingly close to the 20 GB being chased, and entirely an artifact. Summed
  over distinct PIDs only, the same tree is **2.45 GB across at most 4 processes,
  max single member 2.39 GB**. The reported 20 GB was described as a *single*
  process at ~999% CPU (~10 threads), so anyone re-measuring must read
  `/proc/<pid>/status` per PID, never per TID.
- No fix is proposed or landed. Locating *what* inside the interpreter retains
  2.4 GB (module ASTs never released after lowering is the obvious candidate)
  needs allocation instrumentation; attach profiling is blocked on this host
  (`ptrace_scope=1`, `perf_event_paranoid=4`).
- Whether the ~2.4 GB floor and the known `ast:parse_module` time cost
  (lane aa9ca279d669ee1f2) share a root cause is **untested**. Both point at
  `parse_module` over the same corpus, so they plausibly do; that should be
  checked before either lane edits the parser.

## Cheapest next step

Instrument module-AST retention in the seed's interpreted module loader and see
whether ASTs for already-lowered modules are reachable at peak. If they are, the
fix is dropping them, and the negative control is trivially available (re-measure
the no-arg worker run, which must fall well below 2.37 GB).

## Where the 2.4 GB is held (code reading, not measurement)

`src/compiler_rust/compiler/src/module_cache.rs:105-122` declares six
process-lifetime `thread_local!` maps keyed by module path:

- `MODULE_EXPORTS_CACHE: HashMap<PathBuf, Value>`
- `MODULE_CLASSES_CACHE: HashMap<PathBuf, HashMap<String, Arc<ClassDef>>>`
- `MODULE_FUNCTIONS_CACHE: HashMap<PathBuf, HashMap<String, Arc<FunctionDef>>>`
- `MODULE_ENUMS_CACHE: HashMap<PathBuf, HashMap<String, Arc<EnumDef>>>`
- `PARTIAL_MODULE_EXPORTS_CACHE: HashMap<PathBuf, Value>`
- `MODULE_EXPORT_OWNERS`, `MODULES_LOADING`

`clear_module_cache()` exists and is called — but only from the **test runner**
(`driver/src/cli/test_runner/execution.rs:561`, `driver/src/simple_test.rs:309`).
Nothing on the `run`/native-build path ever clears it, correctly so: an
interpreter must keep every `FunctionDef` reachable because any of them may
still be called. **This is therefore a design cost, not a leak** — "release the
ASTs after lowering" is not available to an interpreter, and a fix framed that
way will not work.

That reframes the remedy. The floor is the price of *interpreting* the compiler.
The two directions that can actually move it are (a) not interpreting the worker
— run a compiled `native_build_worker` — or (b) reducing per-`FunctionDef` AST
memory density. `PARTIAL_MODULE_EXPORTS_CACHE` alongside `MODULE_EXPORTS_CACHE`
is the one candidate for straightforward duplicate retention and is worth
measuring first, but it has not been measured.

## Explicit non-verification

Any fix here requires rebuilding the Rust seed. Roughly 15 lanes depend on the
current `bin/simple`, so **no rebuild was performed and no fix is verified.**
Everything above the "Where the 2.4 GB is held" section is measured; that
section is code reading only.

## Update: `--entry-closure` settles the discriminator

Reported by the campaign coordinator after the measurements above: the admission
planner build that reached 20 GB **was compiling the entire stdlib for a
one-file CLI entry**, and passing `--entry-closure` cut it to
`Build complete: 1 compiled` in seconds.

That closes the question this report left open. Combined with the measurements
here:

- **RSS scales with source-closure size, not with diagnostic count.** The
  diagnostic-count hypothesis was already refuted by the zero-diagnostic 2.37 GB
  floor; the closure knob now supplies the positive half of the discriminator on
  the same entry.
- It also explains why my replication missed the 20 GB. I reproduced the
  bootstrap's `--source` roots but **not** its environment. The bootstrap runs
  `SIMPLE_BOOTSTRAP=1` (`produce-bootstrap-planner-admission-v2.shs:151`), and
  `native_project/compiler.rs:869` has a bootstrap export-discovery path that
  logs `[llvm-entry-closure] ... unresolved call(s) ... before codegen`. Without
  that env my run took the narrow closure (`source_closure 6/6`); the bootstrap's
  takes the whole-stdlib one. The env, not the argv, is the switch — that is the
  specific thing my earlier "untested remaining difference" note was pointing at,
  now corroborated.

So there are **two separable costs**, and only the second is a bug:

1. a **~2.4 GB fixed floor** to interpret the compiler at all (measured here,
   inherent to the interpreter's module caches, needs a seed rebuild to move); and
2. a **whole-stdlib closure compiled for a one-file entry** (the 20 GB), which
   `--entry-closure` already avoids.

## What a fix must ship with

Per campaign requirement, any fix must land with a runnable bounded-RSS
assertion — a named input plus a peak-RSS threshold, so a regression fails loudly
— together with a negative control that fails when the fix is reverted, and
coverage of the sibling cases. **None of that is in this commit, because no fix
is in this commit.** The natural assertion is: `native-build` of a one-file entry
must not exceed a stated peak RSS; today that measures 2.35 GB and a threshold
set anywhere near 20 GB would be vacuous.

## Host discipline observed

A bootstrap is running and is top priority. The whole-stdlib build that would
reproduce the 20 GB was **deliberately not run** — with 9 GB free, zero swap, and
`earlyoom` reaping the largest process, running it would likely have killed the
bootstrap in order to measure the thing that kills bootstraps. All of this
lane's own measurement processes were terminated to return memory. Nothing was
rebuilt or redeployed.
