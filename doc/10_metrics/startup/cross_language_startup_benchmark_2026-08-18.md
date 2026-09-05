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
