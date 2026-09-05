# Interpreted native-build worker blows up in RSS: two terms, one fixed (~2.7 GB) and one unbounded creep inside `parse`

- **Filed:** 2026-08-18
- **Status:** OPEN — **located, not fixed.** No fix is claimed and no perf claim
  is made: the host was halted mid-measurement (see "Halt" below), so no
  before/after arm exists. This row records what was measured, what it means,
  and exactly where the next owner should put a breakpoint.
- **Predecessor row:** `native_build_source_closure_zero_sources_2026-08-17.md`
  — that row fixed the *misattribution* (`-1` is a shared sentinel for deadline
  expiry AND abnormal child exit, so an allocator abort printed
  `timed out after 7200s`; fixed at `923c5690ccda`). It explicitly deferred the
  blowup itself to "its own row and its own owner". This is that row.
- **Blocks:** `check-native-trailing-default-param`,
  `check-predicate-parser-native-build`, `check-native-object-cache-granularity`,
  `check-native-inprocess-positional-nonvacuous`. None of the four were re-run
  here — see "Not done".

## Binary identity and host state for EVERY number below

`bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
size **59581296**, mtime **2026-08-18 00:21:41 UTC**. Self-reported as the Rust
bootstrap seed, so the native-build worker runs INTERPRETED.

This is the **fourth** distinct binary at that path in one day (59617400 @
12:54:48, 59537240 @ 12:58:51, 59621024 @ 20:28:24, 59581296 @ 00:21:41). Numbers
from the earlier rows were taken on binaries that no longer exist at that path.

Host: `/proc/loadavg` **53.93 → 69.05** across the window, 43-73 runnable of
~1632 threads, ~89-105 concurrent `simple` processes from ~11 other lanes, zero
swap, earlyoom live at 10% free. **Wall-clock numbers below are load-inflated
envelopes.** RSS and CPU-time are the load-robust quantities and are what the
conclusions rest on.

## Reproducer

```
SIMPLE_BOOTSTRAP=1 bin/simple native-build \
  --source test/fixtures/native_trailing_default_param \
  --entry  test/fixtures/native_trailing_default_param/main.spl \
  --entry-closure -o <out>.bin
```

Fixture is **2 files** (`main.spl`, `dep.spl`), a few dozen lines total. The
worker sampled is the grandchild
`bin/simple run src/app/cli/native_build_worker.spl ...` (pid 1792914), NOT the
thin `native-build` parent (which stayed at 33 MB throughout). Sampling:
`ps -o etimes=,rss=,vsz=,time=` every 10 s.

## The RSS curve (VERIFIED — process was alive and progressing at every sample)

| t (s) | RSS | VSZ | CPU time | phase per `build.log` |
|---|---|---|---|---|
| 103 | 2.39 GB | 3.36 GB | 0:58 | no `[build]` line emitted yet |
| 113 | 2.60 GB | 3.36 GB | 1:05 | no `[build]` line emitted yet |
| 124 | 2.74 GB | 3.36 GB | 1:11 | `load_sources 3/3` → `parse 0/2` |
| 134 | 2.74 GB | 3.36 GB | 1:18 | `parse 0/2` |
| 144 | 2.74 GB | 3.36 GB | 1:23 | `parse 0/2` |
| 154 | 2.74 GB | — | 1:28 | `parse 0/2` |
| 164 | 2.75 GB | — | 1:32 | `parse 0/2` |
| 174 | 2.75 GB | — | 1:38 | `parse 0/2` |
| 184 | 2.75 GB | — | 1:43 | `parse 0/2` |
| 194 | 2.74 GB | — | 1:48 | `parse 0/2` |
| 205 | 2.75 GB | — | 1:53 | `parse 0/2` |
| 215 | 2.74 GB | 3.36 GB | 1:57 | `parse 0/2` |
| 225 | 2.75 GB | 3.36 GB | 2:00 | `parse 0/2` |
| 245 | 2.81 GB | — | 2:08 | `parse 0/2` |
| 256 | 2.88 GB | — | 2:13 | `parse 0/2` |
| 266 | 3.02 GB | — | 2:18 | `parse 0/2` |
| 278 | 3.15 GB | — | 2:24 | `parse 0/2` |

CPU/wall ≈ 52% throughout — consistent with the load, not with idling or a hang.
The run was **killed by this lane** at t≈290 s under the halt order; the curve
above is a measurement up to that point, and no point in it is a killed sample.

## Control: the interpreter itself is 20 MB, not 2.7 GB (VERIFIED)

```
fn main() -> i64:
    0
```

`SIMPLE_EXECUTION_MODE=interpret bin/simple run a.spl`, `/usr/bin/time -f`:
**maxrssKB=20992** (20.5 MB), wall=0.64s, user=0.02, sys=0.20, **rc=0**.

So the 2.74 GB is *entirely* the worker's import-closure load. A second control
(the same file plus one `use app.io._CliCompile.compile_targets.{cli_native_build}`
whose body never calls it) was **killed by the halt before it finished — that is
an UNVERIFIED lower bound, not a measurement, and is deliberately not reported
as a number.** It is the single cheapest next measurement and is described under
"Next steps".

## Two distinct terms — and the answer to "(a) proportional or (b) leak" is BOTH

**Term 1 — fixed ~2.74 GB, spent BEFORE any pipeline step. Shape (a).**
No `[build]` line at all is emitted for the first ~100 s, and RSS reaches
2.74 GB in that window. This is the cost of the interpreted seed loading the
worker's whole `compiler.driver` + LLVM import closure. It is proportional to
**the compiler**, not to `--source` — a 2-file `--source` pays it in full. This
is legitimately proportional work, but to the wrong thing; shrinking `--source`
cannot touch it. Fixing it is a redesign (a cached/serialised module image, or a
non-interpreted worker), not a small change, and is **not** attempted here.

**Term 2 — unbounded creep of ~1.3 MB/s INSIDE `parse`. Shape (b).**
From t=124 s to t=278 s RSS went 2.74 → 3.15 GB (~410 MB in 154 s) while the
`parse` counter stayed pinned at **`0/2`** — zero of two files parsed, on a
fixture of a few dozen lines. There is no source-set quantity that 410 MB and
180 s of CPU can be proportional to here. **This is retention/work that should
not exist**, and it is the term that kills the guards: extrapolated over the
worker's 7200 s budget it is ~9 GB on top of term 1, which is exactly the
15-17 GB workers the predecessor row observed on the same fixture, and is the
same order as the "~1 GB per 30 s" stage-3 figure. It is also why the abort is
an allocator abort and not a deadline expiry.

Note the plateau at t=134-225 s and the resumption at t≥245 s: the creep is not
smooth, which is consistent with a growth-by-doubling buffer rather than a
steady per-item leak — see the 2^31 datum below.

## Leading hypothesis: the retention is in the interpreted parse path — SUPPORTED

The lint lane measured independently, tonight, that **98% of `simple lint` wall
time is `ast:parse_module`** (`parse_module_silent_checked`,
`entry_and_fixes.spl:71`) with a real-code cost exponent ~1.46, all 33 lint rules
together ~2%. That is the same pure-Simple compiler parser running interpreted
under the same seed.

Evidence here **supports** that hypothesis: term 2 accrues entirely within the
`parse` step, with the step counter not advancing. It does **not** prove it —
nothing here identifies the specific allocation, and the `parse` step emitter
could be attributing time that is really spent in a callee.

What term 2 is **not**: it is not diagnostic accumulation. `8ea9c62d05b8`
(bounded diagnostic retention) already addressed that class, and the creep here
continues long after the warning flood in `build.log` has stopped.

## The strongest untaken measurement, and why it is untaken

The predecessor row recorded `memory allocation of **2147483648** bytes failed`
— **exactly 2^31 in a single request**, on a one-module fixture. That is one
contiguous buffer doubling from 1 GiB, not diffuse growth. A backtrace at that
allocation names the defect outright.

Setup that was built and running when the halt landed:

```
ulimit -v 6000000
gdb -q -batch -x cmds --args $(readlink -f bin/simple) run \
  src/app/cli/native_build_worker.spl --source <fixture> --entry <fixture>/main.spl \
  --entry-closure -o <out>.bin
```

with `break __rust_alloc_error_handler` / `break rust_oom` / `break abort`.
It reached 2.88 GB at t=164 s and was killed by this lane at the halt — **no
backtrace was obtained; UNVERIFIED.**

**Useful finding for whoever repeats this:** the deployed binary is
`not stripped, with debug_info` (12 debug sections), but
`__rust_alloc_error_handler` and `rust_oom` do **not** resolve — both breakpoints
stayed *pending*. Only `break abort` resolved (`Breakpoint 3 at 0x28252e0`). Use
`abort`, or `alloc::alloc::handle_alloc_error`, not the two obvious names.

## Halt

Work stopped on coordinator order at 12:45 UTC 2026-08-18: 1 GB free of 125 GB,
22 GB available, **14 earlyoom kills in the preceding 15 minutes**, 105
concurrent `simple` processes, load 63. All of this lane's runs (repro, gdb abort
run, gdb sampling run, import-cost controls, samplers — pids 1792776/1792793/
1792794/1792909/1792914/1798351/1807521/1803167/1803173/1803174/1803548/1836393/
1836394/1836395/1850334/1850336/1850909) were killed by this lane; no other
lane's processes were touched. On a box in that state an RSS curve measures
thrashing, and a 9 GB-bound job is earlyoom's first pick, so any further sample
would be a lower bound rather than a measurement.

## Not done (stated rather than implied)

- **No fix.** No code change is proposed or landed by this row.
- **No before/after.** There is no reverted arm, so no perf claim is made.
- **The four guards were NOT re-run.** Their verdicts are unchanged and unknown
  as of this row.
- Control `b` (import-cost isolation) and the gdb abort backtrace: both killed,
  both UNVERIFIED.

## Next steps, in cost order

1. **On an idle box**, `/usr/bin/time -f %M` the two-line control that imports
   `app.io._CliCompile.compile_targets` and never calls it. That splits term 1
   from term 2 with one cheap run and no instrumentation.
2. **Get the abort backtrace.** `break abort` (not `rust_oom`), `ulimit -v` to
   force it early, `bt 60`. The 2^31 single allocation should name one buffer.
3. Only then decide between fixing the identified retention (term 2, small
   change, likely in the interpreted `parse_module` path) and filing term 1 as
   the redesign it is.
