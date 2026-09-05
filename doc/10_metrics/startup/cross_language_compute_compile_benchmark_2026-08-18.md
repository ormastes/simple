# Cross-Language Compute + Compile Benchmark (2026-08-18)

## Environment

- Host: Linux 6.8.0-137-generic, shared box — `uptime`: up 8 days 19:41, load average 3.33 / 2.50 / 2.19 at measurement time. Treat numbers as an envelope, not a clean-room result.
- Simple binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`, 59,673,480 bytes, mtime **2026-08-18 06:12:48** (redeployed with the env-cache; `--version` self-identifies as the Rust-built seed). Rows labelled *(old bin)* were measured ~04:28 on the pre-redeploy binary of the same day; *(new bin)* rows were re-run on the 06:12 binary.
- Toolchains: go (`/usr/bin/go`), rustc (`~/.cargo/bin/rustc`, `-O` = opt-level 2), cc (`/usr/bin/cc`, `-O2`), python3, bun (`~/.bun/bin/bun`).
- Method: wall-clock p50 of 5 runs (`date +%s.%N` bracketing, `timeout 300`), plus one `/usr/bin/time -v` run for Max RSS. Simple headline mode is `bin/simple run` = **Cranelift JIT**; interpreter mode noted separately.
- Sources/fixtures: scratchpad `xbench2/` (loop.spl/str.spl/arr.spl and per-language equivalents; `arith.*` compile fixtures, 125 functions / ~501 lines each).

## Compute results (p50 of 5, seconds; Max RSS kB)

### (a) Iterative 10^8 int-add loop

| lang | p50 | RSS kB | note |
|---|---|---|---|
| C -O2 | 0.005 | 2,048 | loop likely folded |
| Rust -O2 | 0.005 | 2,048 | loop likely folded |
| Go | 0.102 | 2,048 | |
| Simple JIT (new bin) | **0.295** | ~27,900 | old bin: 0.477 |
| Simple interp | 1.151 | 22,272 | 3 runs, old bin |
| Bun (f64 loop) | 0.201 | 39,424 | integer-op variant: 12.057 |
| Python3 | 22.666 | 10,496 | |

### (b) 100k string appends ("abcdefgh" each)

| lang | p50 | RSS kB |
|---|---|---|
| C -O2 | 0.008 | 2,048 |
| Rust -O2 | 0.010 | 2,816 |
| Go | 0.022 | 5,120 |
| Bun | 0.054 | 39,680 |
| Python3 | 28.795 | 12,812 |
| Simple JIT | **259.3 (single run)** | n/a — first attempt hit `timeout 300`; one 580s-cap run completed. Clearly quadratic (O(n^2) copy-per-append). |

### (c) 10^7 array push + sum

| lang | p50 | RSS kB | note |
|---|---|---|---|
| C -O2 | 0.081 | 79,360 | |
| Rust -O2 | 0.095 | 79,616 | |
| Go | 0.106 | 79,872 | |
| Bun | 0.375 | 305,300 | |
| Simple JIT (new bin) | **0.846** | ~218,000 | old bin: 2.399 |
| Python3 | 2.348 | 402,432 | |

## Compile speed (~500-line generated arithmetic file, 125 fns, p50 of 5)

| toolchain | p50 |
|---|---|
| bun build | 0.013s |
| python3 -m py_compile | 0.045s |
| rustc --emit=metadata | 0.062s |
| go build | 0.114s |
| rustc -O (full) | 0.136s |
| cc -O2 -c | 0.254s |
| **bin/simple lint** (new bin) | **76.5s** (repeat: 75.6s) |

The lint number is a large improvement over the historical envelope in
`.claude/rules/commands.md` (2026-08-17: 90 tiny fns / 361 lines = **436s**;
this 125-fn / 501-line fixture = 76.5s, roughly 6-10x better per declaration)
following the root cause identified — and now fixed and deployed in the
2026-08-18 06:12 binary — in
`doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md`.

### SIMPLE_LINT_PROFILE=1 phase table (std easy-fix rules, aggregated)

| rule phase | total |
|---|---|
| check_deprecated_if_let | 97.2 ms |
| check_unnamed_duplicate_typed_args | 69.5 ms |
| dup_args:collect_signatures | 69.2 ms |
| check_short_grammar_refactor | 59.4 ms |
| check_stub_impl_text | 51.4 ms |
| check_resource_leak | 16.1 ms |
| check_parser_contextual_keyword / non_exhaustive_match | ~15 ms each |
| remaining rules | <1 ms |

Std-rule scanning totals **~0.4s of the 76s wall** — the cost lives in fixed
startup (~12s historical) plus the semantic/type-check pass, not in the text
rules.

## Gap-to-best summary (best = fastest per row)

| benchmark | Simple JIT vs best | vs closest managed peer |
|---|---|---|
| int loop 1e8 | ~59x vs C/Rust (0.295 vs 0.005) | 2.9x vs Go; 68x faster than Python |
| string append 100k | ~32,000x vs C (259s vs 0.008) | 9x slower than Python even |
| array 1e7 | ~10x vs C (0.846 vs 0.081) | 2.3x vs Bun; 2.8x faster than Python |
| compile 500 lines | ~300x vs cc -O2 (76.5s vs 0.254s) | — |

## Top-3 bottlenecks

1. **Quadratic string append in JIT** — `s = s + "…"` copies the whole string
   each iteration (no capacity-doubling buffer / rope). 259s where every peer
   is <0.06s except naive Python. Worth a builder fast-path or amortized
   `String` growth. (No existing bug record found; candidate for filing.)
2. **Lint fixed + semantic overhead** — 76.5s for 501 lines even after the
   `lint_timeout_hwir_zca_rows_2026-08-17` fix; profile shows std rules at
   ~0.4s, so ~99% is startup + semantic analysis. Crosslinks:
   `doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md`,
   `.claude/rules/commands.md` (Fast Path table — pre-fix numbers, see dated
   note there), `scripts/check/lint-cached.shs` (warm-cache mitigation).
3. **Array/loop codegen gap (~10x vs C, ~3x vs Go)** — boxed dynamic-array
   values and per-element tag handling dominate; RSS is 2.7x C for the same
   payload. The env-cache redeploy already improved loop 1.6x and arr 2.8x in
   one day; remaining gap is value representation, not startup.
