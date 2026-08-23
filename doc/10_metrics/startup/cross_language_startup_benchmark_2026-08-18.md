# Cross-Language Startup Benchmark — 2026-08-18

Hello-world startup time, max RSS, and binary size for Simple vs Go, Python3,
Bun, Rust, C. Workbench: session scratchpad `xbench/` (not committed).

## Environment

- Host: shared Linux box, **load average 23.8/33.4/31.1** at run time — treat
  all numbers as an envelope, not a clean-room measurement.
- Simple binary: `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`
  (59,620,392 bytes, mtime 2026-08-18 01:08). `--version` confirms it is the
  **Rust bootstrap SEED**, not the self-hosted binary. All Simple results here
  attribute to the seed's interpreter path.
- `bin/simple native-build hello.spl` **fails** on the seed ("native-build
  worker exited with code 1"), so no Simple compiled-binary lane could be
  measured; interpreter (`run`) only.
- Toolchains: go 1.22 (`/usr/bin/go`), python3 3.12, bun 1.3.11, rustc 1.91
  (`-O`), cc `-O2`.
- Method: p50 of 8 timed runs after 1 dropped warmup, `date +%s%N` bracketing.
  RSS: `/usr/bin/time -v` Maximum resident set size, single run (noisy box).

## Startup time (p50, ms)

| lane | p50 ms | raw runs (ms) |
|---|---:|---|
| C binary | 4 | 4 3 4 6 4 3 3 5 |
| Rust binary | 4 | 5 4 4 4 4 5 4 5 |
| Go binary | 7 | 6 7 8 7 6 8 9 9 |
| Simple `--version` (process floor) | 16 | 14 15 14 16 22 19 18 22 |
| `bun run hello.js` | 31 | 30 33 29 39 37 30 31 37 |
| **Simple `run hello.spl` (seed interpreter)** | **31** | 56 303 147 94 31 23 21 26 |
| `bun hello.js` | 33 | 45 32 29 34 38 32 37 33 |
| `python3 hello.py` | 43 | 43 42 45 53 49 50 43 41 |
| `go run hello.go` (script mode) | 245 | 284 255 234 245 213 240 254 264 |

Note the Simple run sequence: first timed runs were 56–303 ms, settling to
~21–31 ms once page cache warmed — cold-cache startup is several-fold worse
than the p50 suggests.

## Memory (max RSS, KB, one run)

| lane | max RSS KB |
|---|---:|
| C binary | 1,280 |
| Go binary | 1,792 |
| Rust binary | 1,792 |
| python3 | 10,496 |
| **Simple `run` (seed)** | **22,272** |
| bun | 31,744 |
| `go run` | 45,056 |

## Binary size (bytes)

| artifact | bytes | stripped |
|---|---:|---:|
| C `-O2` | 15,960 | 14,472 |
| Rust `-O` | 3,896,744 | 363,680 |
| Go | 1,893,889 | 1,231,928 |
| **Simple seed binary (interpreter, whole toolchain)** | **59,620,392** | n/a (not per-program) |
| Simple native-build output | — | fails on seed |

Not apples-to-apples: Simple has no per-program binary here; 59.6 MB is the
entire compiler/interpreter, the price of distribution in interpreter mode.

## Loader angle (Simple)

- `strace -c -e openat bin/simple run hello.spl`: **31 openat calls (14
  ENOENT)** — a no-import hello does NOT pull the 82-open stdlib sweep; loader
  I/O is not the startup driver for trivial scripts.
- `bin/simple --version` p50 16 ms is the process-overhead floor; `run` adds
  ~15 ms of parse/interp setup warm.

## Gap to best competitor

- **Startup:** Simple 31 ms vs C/Rust 4 ms (~8x), vs Go binary 7 ms (~4.4x) —
  but Simple's fair peers are script runtimes: it matches bun (31–33 ms) and
  beats python3 (43 ms) and `go run` (245 ms) warm.
- **Memory:** 22.3 MB vs C's 1.3 MB (~17x), vs python3 10.5 MB (~2.1x); better
  than bun (31.7 MB).
- **Binary size:** worst gap by far — 59.6 MB toolchain vs a 14 KB stripped C
  hello; no working native-build lane on the seed to close it.

## Caveats

- Shared box under heavy load; single-run RSS; p50 masks cold-start outliers.
- Seed-not-selfhosted: numbers do not characterize the pure-Simple binary.
- No JIT/native lane measured for Simple (native-build worker failure, noted
  above); competitors' compiled lanes are fully optimized builds.

---

# Re-measurement 2026-08-23 — the Simple **native-binary** lane, measured for the first time

This section EXTENDS the 2026-08-18 measurement above; it does not replace it.
The older rows stand as history. Two things changed:

1. The 2026-08-18 doc could not measure a compiled-Simple lane at all
   ("`bin/simple native-build hello.spl` **fails** on the seed"). **That blocker
   was root-caused and fixed in this commit** — the seed's interpreter extern
   table had no `rt_heap_ref_wellformed` adapter, which killed every
   native-build. See
   `doc/08_tracking/bug/seed_interpreter_extern_missing_rt_heap_ref_wellformed_2026-08-23.md`.
2. Every number below was taken with `hyperfine` **absent from this host** — a
   careful `date +%s%N` loop was used instead (30 timed runs per lane, no warmup
   dropped), plus one `/usr/bin/time -f %M` run for max RSS.

## Environment and the load caveat — read this before quoting any number

The box is **heavily loaded by other lanes** and load moved substantially
*during* the session. A number without its load average is misleading here, so
each block below carries its own `uptime`. Do not compare a row from block A
against a row from block B.

- Host: Linux 6.8.0-137-generic, shared.
- Simple binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
  **60,638,704 bytes**, built in this session with `cargo build --release --bin simple`
  from `origin/main` `c1efb59cf09` **plus the extern-adapter fix**. `--version`
  self-identifies as the Rust bootstrap SEED. No pure-Simple full CLI binary is
  deployed, so the `run` rows are still the seed's JIT/interpreter path.
- Toolchains present: go (`/usr/bin/go`), python3, bun (`~/.bun/bin/bun`),
  node (`/usr/bin/node`), strace, nm.
  **Absent: `hyperfine`** (method above). rustc/cc not re-measured this session.
- Fixtures: `hello.spl` / `.go` / `.py` / `.js` (3 lines, no imports) and a
  trivial-import variant per language.

### Block A — load average **23.6 / 32.5 / 33.1** (08:51)

Times in **milliseconds** (harness emits microseconds; converted here).

| lane | median | min | p95 | max RSS KB |
|---|---:|---:|---:|---:|
| Go native binary | 4.0 | 3.1 | 7.4 | 1,536 |
| python3 hello | 27.6 | 24.6 | 41.9 | 10,496 |
| bun hello | 35.9 | 25.9 | 94.5 | 32,512 |
| python3 + 3 imports | 43.2 | 32.5 | 59.1 | 11,008 |
| bun + 1 import | 58.3 | 46.9 | 67.8 | 38,656 |
| node hello | 58.6 | 44.8 | 78.9 | 46,592 |

### Block B — load average **22.4 / 31.0 / 32.6** (08:52), Simple `run` path

| lane | median | min | p95 | max RSS KB |
|---|---:|---:|---:|---:|
| `simple --version` (process floor) | 30.5 | 16.8 | 81.3 | 14,080 |
| `simple run hello.spl` | 76.3 | 36.3 | 241.2 | 39,336 |
| `simple run imp.spl` (1 stdlib import) | 74.1 | 30.0 | 146.4 | 31,488 |

### Block C — load average **46.0 / 38.6 / 34.6** (09:05), all lanes together

This block is the only internally-comparable one, because everything in it was
measured back-to-back under the same (high) load. **Quote this block, not a
cross-block comparison.**

| lane | median | min | p95 | max RSS KB | artifact size |
|---|---:|---:|---:|---:|---:|
| **Simple native binary** | **9.8** | 6.2 | 15.7 | **1,280** | **22,264 B** |
| Simple native, `--mode dynload` | 10.1 | 6.7 | 16.7 | 1,280 | 22,264 B (identical — see below) |
| Go native binary | 14.5 | 6.1 | 22.5 | 1,536 | 1,893,897 B |
| python3 hello | 82.6 | 38.4 | 99.7 | 10,496 | — |
| bun hello | 85.8 | 43.3 | 119.4 | 32,256 | — |
| `simple --version` (floor) | 89.3 | 27.5 | 256.0 | 14,080 | 60,638,704 B |
| `simple run hello.spl` | 143.6 | 53.6 | 406.5 | 27,392 | — |

## Verdict on launch overhead

**A natively-built Simple binary is competitive and then some.** At 9.8 ms
median it beat Go's compiled binary (14.5 ms) in the same block, with a smaller
RSS (1,280 vs 1,536 KB) and an artifact **85x smaller** (22 KB vs 1.9 MB,
dynamically linked against libc only). It is ~8x faster to start than python3 or
bun. Simple's launch overhead is **not** a problem — the problem was that this
lane could not be built at all until today.

**The `run` path is a different story and should not be quoted as "Simple's
startup".** At 143.6 ms (block C) / 76.3 ms (block B) it is the slowest lane
measured. Roughly a third to a half of that is the process floor —
`simple --version`, which compiles nothing, still costs 89.3 / 30.5 ms.

## Where the `run`-path time goes — and a correction to a widely-cited number

`.claude/rules/commands.md` cites "**82 opens of `src/lib/**.spl`, zero `.smf`**"
on every process start. **That is not what a hello-world run does**, and citing
it as a general startup cost is wrong. Measured directly:

```
$ strace -f -c -e trace=openat,open,stat,mmap bin/simple run hello.spl
 61.49%  0.001129s   89 openat (14 errors)
 37.47%  0.000688s   35 mmap
--> 1.84 ms of syscall time TOTAL; 5 of the 89 opens are .spl files
$ strace -f -e trace=openat bin/simple run imp.spl | grep -c '\.spl"'
7                      # one stdlib import adds two opens, not eighty
```

So file I/O accounts for **under 2 ms** of a 76-144 ms run. The 82-open figure
describes a run that pulls in the std-importing compiler surface, not a bare
program, and the original claim in `commands.md` is about *stdlib editing not
needing a build* — a correct claim being misread as a startup cost.

The real floor is the **60.6 MB binary**: `--version` does no compilation and
still costs 30-89 ms, tracking load almost exactly (its p95 of 256 ms under load
46 is the tell). That is page-fault and dynamic-relocation cost on a very large
executable, not parsing and not I/O. The remaining ~45 ms of `run hello.spl` is
parse + Cranelift JIT.

**Actionable, filed rather than hand-waved:** the `run` floor is a binary-size
problem. The measured fix direction is the one this session already demonstrated
— a natively-built 22 KB artifact starts in 9.8 ms. Nothing here argues for
micro-optimising the loader.

## Trivial-import row: honestly missing for the native lane

`native-build` of a fixture with one stdlib import
(`use std.common.text.{trim}`) still fails:

```
error: MIR lowering error: unresolved method call: index_of
```

so there is **no** "Simple native binary + import" row above. This is a second,
separate defect recorded in §5 of the extern bug record. It is not estimated and
not interpolated.

## `--mode dynload` produced nothing extra

Recorded here because it directly affects the artifact-size column: building the
same hello with `--mode dynload` produced a file **byte-identical** to the
`one-binary` build (`cmp` clean), with **no diagnostic of any kind**. See
`doc/08_tracking/bug/aspect_dynload_producer_absent_and_mode_silent_downgrade_2026-08-23.md`.

## Related

- Compute + compile-speed companion:
  `doc/10_metrics/startup/cross_language_compute_compile_benchmark_2026-08-18.md`
  (its pre-06:12 rows predate the 2026-08-18 seed redeploy and are labelled
  *(old bin)* there).
