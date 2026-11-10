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

## 2026-11-07 — re-measured on Windows (round 15); floor is 1.99 GB, and ~1.3 GB of it is already live after 100 module loads

Binary: `simple-base.exe` built from `origin/release/1.0.0` tip `4eb1de2ecbd`
(bootstrap profile, 17883136 B, sha256 `c0c47b2cdd6cd6ee…`), Windows 11,
`SIMPLE_MEM_TRACE=1 SIMPLE_EXECUTION_MODE=interpret
sh scripts/perf/measure-peak-rss.shs -- simple-base.exe run src/app/cli/native_build_worker.spl`
(no args — compiles nothing, exactly the 2.37 GB case above).

| quantity | 2026-08-18 (Linux) | 2026-11-07 (Windows) |
|---|---|---|
| peak RSS, no-arg worker | 2.37 GB | **1.99 GB** (`peak_kib=1993300`, wall 62.6 s, exit 1) |
| live after 100 module loads | — | **1344.5 MB** (peak 1351.3 MB) |
| live after 500 module loads | — | 1475.7 MB |
| live after 1000 module loads | — | (see mem log) parse_retained=473.4MB eval_retained=299.5MB |
| import_bindings / module_envs at 500 loads | — | 39,624 / 500 |

Two things the earlier record could not see:

1. **The floor is front-loaded, not accumulated.** 1.34 GB is live after the
   first 100 of ~1000 module loads and the next 400 loads add only 130 MB.
   `parse_retained + eval_retained` at 500 loads is 431 MB, so roughly 1 GB
   of the live set is neither parse nor eval retention as the census
   classifies it. That unattributed early gigabyte is the next thing to
   attribute (the census prints its first line only at 100 loads; a
   per-10-load or per-phase first report would say whether it is the runtime
   symbol seeding, the prelude, or the first few large generated modules
   such as `20.hir/generated/hir_codec.spl`, 10.2 MB self + 17.2 MB parse).
2. `import_bindings=39,624` for 500 envs (79 per module) versus the 927,167
   / 667 envs (1,390 per module) the 2026-08-21 shard census reported: the
   per-importer copies named in memory_retention_compiler_and_interpreter
   § "Open" are gone (`record_owner_binding_layer` shares the source table
   by reference). That part of the mechanism is fixed; the floor that is
   left is the early term above.

No fix landed in this pass; the measurement harness is
`scripts/perf/measure-peak-rss.shs` (ps-sample on Windows, exact
PeakWorkingSet) and the numbers above are the baseline a budget gate on this
host would be set against.

## 2026-11-10 status — LIVE-blocked-by-scope (P3 bootstrap lane row 43, work/p3-boot6-20261110)

Re-judged on this lane's base (`4343ce254922`): still LIVE. The 2026-11-07
Windows re-measurement in this record (1.99 GB no-arg floor on
`simple-base.exe` tip `4eb1de2ecbd`) stands as the current baseline; nothing
in the 25 merges on this base changes the worker spawn shape
(`bin/simple native-build` still spawns `run src/app/cli/native_build_worker.spl`
interpreted) or the seed's module-cache retention design
(`src/compiler_rust/compiler/src/module_cache.rs`, six process-lifetime
thread_local maps, cleared only by the test runner). Both remedy directions
named in this record are outside the bootstrap-tooling scope: (a) running a
compiled `native_build_worker` is the self-host bootstrap redesign itself
(chicken-and-egg by definition), and (b) per-`FunctionDef` AST density /
`PARTIAL_MODULE_EXPORTS_CACHE` duplicate retention is `src/compiler_rust`
(seed-fix lane, excluded) or `src/compiler` (agent-30 lane, excluded).

Fix sketch for the owning lane: instrument the seed's interpreted module
loader to census `PARTIAL_MODULE_EXPORTS_CACHE` vs `MODULE_EXPORTS_CACHE`
live bytes after the no-arg worker run; if duplicate retention is confirmed,
drop the partials table on successful module completion and re-measure the
no-arg floor (must fall well below 1.99 GB). If it is not confirmed, the
floor is intrinsic interpreter cost and the only honest fix is (a).

BLOCKED-needs-grant (heavy build forbidden on this lane): seed rebuild to
land/verify any retention fix —
`(cd src/compiler_rust && cargo build --profile bootstrap -p simple-driver && cargo build --profile bootstrap -p simple-native-all --features driver-compat)`
— plus re-measure via
`SIMPLE_MEM_TRACE=1 sh scripts/perf/measure-peak-rss.shs -- bin/simple.exe run src/app/cli/native_build_worker.spl`.
No measurement re-run this pass: 2026-11-07 baseline on the same host shape is
already in-record and a re-run would only re-print it (budget rule: no
identical reruns).
