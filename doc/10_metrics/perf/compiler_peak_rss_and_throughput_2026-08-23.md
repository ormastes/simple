# Compiler performance & memory measurement — 2026-08-23

Closes the standing **peak-RSS "zero-by-absence"** gap: prior sweeps reported
"0 SIGSEGV/SIGTERM deaths" with peak RSS *never measured*. It is measured here.

## Measurement identity (cite with every number)

| item | value |
|---|---|
| binary | `bin/release/x86_64-unknown-linux-gnu/simple`, **60,650,360 B**, mtime 2026-08-23 04:47:05 UTC |
| sha256 | `f6521b60b67d38944016b82451ac60c522375410c60dec7178d5c06bd063bde7` |
| provenance | **Rust bootstrap seed** — it prints its own "seed only, build the pure-Simple bin/simple instead" warning. No full-CLI pure-Simple binary is deployed, so every number below is a SEED number. |
| tree | `origin/main` @ `61535e69437`, worktree `/mnt/data/worktrees/perfmem-1` (frozen copy of the binary, so another lane replacing `simple-main`'s symlink cannot contaminate the series) |
| box | 32 CPU, 125 GiB RAM, load 16–30 throughout (shared, many concurrent lanes), MemAvailable 68–72 GiB |
| env | `SIMPLE_TIMEOUT_SECONDS=0` |
| earlyoom | kills `simple` (designated victim) at ~3.7 GiB per process — peak RSS is a **safety** budget, not a nicety |

## Baseline gate

`sh scripts/check/check-perf-regression-tests.shs` → `PASS — 176 mechanism(s)
checked, 0 regressed`. (The standing docs say "16 rows"; it is now **176**.
That figure is stale wherever it appears.)

## Table 1 — per-compile wall time and peak RSS (`/usr/bin/time -v`, 3 reps)

| workload | reps | wall (min/med/max) | peak RSS | rc | load | MemAvail |
|---|---|---|---|---|---|---|
| `hello.spl` — 3 lines, no imports (`compile --format=smf`) | 3 | 0.03 / 0.15 / 0.17 s | **29.7 MB** (29696/29952/30464 kB) | 0 | 17.7 | 71.6 GiB |
| `src/app/cli/bootstrap_main.spl` — 807-module closure, ~14 MB source | 3 | 23.07 / 23.41 / 29.29 s | **1.55 GiB** (1606496/1625444/1619160 kB) | 1 (see below) | 16.7–17.4 | 68–72 GiB |

Ratio: a no-import hello costs 30 MB; the compiler's own closure costs **54x**
that, from a single process, against a 3.7 GiB kill threshold — i.e. the seed
compiling its own closure already spends **42 % of its per-process death budget**
before MIR/codegen is even reached.

## Table 2 — the retention curve (the headline finding)

RSS sampled every 200 ms through one `compile` of the 807-module closure
(load 23.9; sampling adds ~2x wall, so read the SHAPE here and the wall from
Table 1):

| t | 0s | 5s | 10s | 15s | 19s | **20s** | 25s | 35s | 45s | 52s |
|---|---|---|---|---|---|---|---|---|---|---|
| RSS | 51 MB | 251 | 471 | 906 | 1232 | **1571** | 1571 | 1572 | 1572 | 1573 |

Monotonic climb through module load + parse, then **perfectly flat at 1571 MB
for the remaining 32 s (62 % of the run) — not one byte released.** The whole
closure's AST is retained live for the entire semantic phase by the
`IMPORTED_MODULE_AST` memo
(`src/compiler_rust/compiler/src/hir/lower/import_loader.rs:33`), whose only
clear site is the global `clear_module_cache`
(`module_cache.rs:191`) — never at end-of-lowering. This independently
reproduces, and quantifies the tail of, the note in
`src/compiler_rust/parser/tests/ast_size_budget.rs`.

## Status of the "known open defects"

| item as briefed | actual state at `origin/main` @ `61535e69437` |
|---|---|
| `IMPORTED_MODULE_AST` 112x blowup, "open, unfixed" | **The re-parse defect is FIXED and pinned** — the memo exists and `imported_module_ast_memo_tests::repeated_import_of_the_same_module_parses_it_exactly_once` pins it by parse COUNT (N visits ⇒ exactly 1 parse). What is live is the *opposite* trade: the memo's **retention** (Table 2). Briefing is stale. |
| Node 936 B → 504 B (`ee40943016a`), "check for similar wins" | **Landed and ratcheted** — `parser/tests/ast_size_budget.rs` pins `Node`/`FunctionDef` ≤ 560 B and `Expr` ≤ 128 B, and separately asserts `contract`/`return_constraint` stay `Option<Box<_>>` (8 B, niche-optimised) rather than 336 B/112 B inline. |
| MIR aggregate slot-size vs 8-byte stride | Untouched by design — briefed as fixable only jointly with SIMD `size_bytes()`. Not attempted. |

## Correctness observations (NOT perf; filed, not fixed here)

`origin/main` @ `61535e69437` cannot compile its own driver with this seed:

- `src/app/cli/bootstrap_main.spl` → `semantic: Undefined("undefined identifier: panic")`
- `src/app/info/main.spl` → `semantic: Undefined("undefined identifier: fetch_index_entry")`

Consequence for measurement, stated rather than papered over: the 1.55 GiB in
Table 1 is the peak of **load + parse + semantic only**. MIR and codegen never
run, so the true single-process peak for a full closure compile is *at least*
this and has not been observed.

## Table 3 — the multi-process native-build path (THE peak-RSS answer)

`native-build` is not one process. The parent stays tiny (54 MB flat for 79 s —
a parent-only sampler reports that and is **wrong**); the memory lives in
`simple run src/app/cli/native_build_worker.spl` children. Sampling matched
processes by `/proc/*/exe` against the frozen binary path (unique to this
worktree, so no other lane's `simple` is counted):

| workload | tree-sum peak | max single process | max concurrent | wall | rc | load |
|---|---|---|---|---|---|---|
| `native-build src/app/any_audit/main.spl` (`SIMPLE_CACHE_SCOPE=perfmem-1`) | 2405 MB | **2351 MB = 2.30 GiB** | 2 (parent + 1 worker) | 93 s | 1 | 26.7 |

2.30 GiB reproduces the briefed 2.28–2.52 GiB per-worker reference band exactly.
**The reference band was itself an under-measurement**, because it was taken at
whatever point the build reached — see Table 4.

## Table 4 — the worker never plateaus (the memory-safety finding)

Driving the worker directly, sampled every 200 ms, two independent runs:

| run | peak observed | state at abort | load |
|---|---|---|---|
| 1 | **2726 MB = 2.66 GiB** | still climbing | 25.5 |
| 2 | **2836 MB = 2.77 GiB** | still climbing | 24.3 |

Run-1 curve (MB, per second): 71 → 400 (5s) → 630 (10s) → 865 (16s) → 1028
(20s) → 1544 (25s) → 1932 (33s) → 2330 (40s) → 2612 (47s) → **2726 (51s)** →
2167 (52s, teardown).

Two things this shows that Table 2 does not:

1. **The worker's peak is ~1.75x the single-process `compile` peak** (2.72 GiB
   median vs 1.55 GiB), because the worker *interprets* `native_build_worker.spl`,
   whose import closure is the whole compiler — it pays the AST retention of
   Table 2 **and** the interpreter's own module-globals/HIR/MIR state on top.
2. **It is monotone and unbounded on this workload, not a plateau.** Over the
   35–51 s window RSS rose 2089 → 2726 MB, i.e. **~40 MB/s, still rising when
   the run aborted.** It aborted on a semantic error, not on completion, so the
   true peak of a *successful* full worker build is strictly greater than
   2.77 GiB and was never reached.

### Headroom arithmetic (why this is a safety finding, not a tidiness one)

earlyoom kills `simple` at ~3.7 GiB ≈ 3789 MB.

| quantity | value |
|---|---|
| highest observed worker RSS | 2836 MB |
| remaining headroom | **953 MB (25 % of budget)** |
| observed growth rate | ~40 MB/s |
| **time-to-kill at that rate** | **~24 s** |

A worker that runs ~24 s longer than the one measured here is SIGKILLed. That
surfaces as `rc=137`/`143` and **reads as a compiler crash while being an OOM
kill** — precisely the misclassification the standing guidance warns about. Any
future growth in the compiler's own import closure spends this 953 MB directly.

## COW-alias class

`sh scripts/check/check-cow-alias-hotpath.shs` →
`PASS — 9680 file(s) scanned, 198 offender(s) checked, 0 new, 0 stale`.
198 offenders remain baselined, none newly introduced. No lint-rule work was
done here — the `perflint-1` lane owns that.

## What was measured vs. not

- **Measured:** single-process peak RSS + wall for a trivial and a 807-module
  closure compile; the full RSS-vs-time curve for both the `compile` path and
  the `native-build` worker; per-worker and tree-sum peak for the multi-process
  native-build path; the COW ratchet; the perf-regression gate.
- **NOT measured, and why:** a cold/warm whole-closure **stage-2** build (the
  `749 compiled, 619.0 s + 95.5 s link` reference). `origin/main` @ `61535e69437`
  cannot compile `src/app/cli/bootstrap_main.spl` with this seed at all (see
  Correctness observations), so that number could not be reproduced or refreshed
  this session. Stated rather than silently dropped.
