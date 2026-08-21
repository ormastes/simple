# Seed interpreter raw throughput (2026-08-21)

Binary: `bin/release/x86_64-unknown-linux-gnu/simple` (seed, e73a0bec647).
Host load 30-55 during measurement (shared box) — treat single samples as an
envelope; large-N runs (50M iterations) make startup/noise negligible and are
the numbers relied on below. Python 3 on the same box is the yardstick.

## Headline: the premise is disconfirmed

The user hypothesis was that the seed interpreter's raw per-op cost explains
~5 s/file. **It does not.** On every shape measured the seed is at parity with
or faster than Python — from 1.05x slower to 38x faster. Nothing is >5x slower
than Python, so the stated defect bar is met by **no** arithmetic/call/dispatch
shape. One shape is a genuine and severe defect, but its mechanism is the
allocator, not interpretation (§ String concat).

## `run` is a hybrid JIT, not a tree-walk interpreter

`src/compiler_rust/compiler/src/compilability.rs` classifies each function:
JIT-compilable, or `RequiresInterpreter(Vec<FallbackReason>)` for pattern match,
closures, string ops, collection literals, actors, generators, etc. Measured on
the *same* 10M increment loop, forcing fallback by adding one list literal to
the function:

| variant | 10M iters | ns/op |
|---|---|---|
| JIT (plain loop) | 485 ms | ~29 (11.5 at 100M) |
| interpreter (fallback triggered) | 1217 ms | ~102 |
| Python 3 | 3839 ms | ~381 |

So the interpreter is ~3.7x **faster** than Python, and the JIT ~33x. Any
per-shape number below must be read knowing which path it took.

## Throughput table

ns/op, measured at 50M iterations unless noted.

| shape | seed ns/op | python ns/op | ratio | path |
|---|---|---|---|---|
| (a) while-loop increment | 11.5 | 381 | **33x faster** | JIT |
| (a') same loop, fallback forced | ~102 | 381 | 3.7x faster | interp |
| (b) 1M calls, fn(2 args) | 16.6 | 636 | **38x faster** | JIT |
| (c) method call on class instance | 25.4 | 477 | **19x faster** | JIT |
| (d) 5M array push + 5M sum | 578 | 429 | 1.35x slower | interp |
| (e2) `char_at` on 10 KB string | 1225 | 1163 | 1.05x slower | interp |
| (f) dict get | 354 | 860 | **2.4x faster** | interp |
| (g) match on enum w/ payload | 182 | ~1000 | **5.5x faster** | interp |
| (h) call touching module global | 259 | (n too small) | faster | interp |
| **(e1) string concat in a loop** | **~793,000/op** | ~11,500/op | **121x slower** | interp |

## The one real defect: string concat is quadratic in kernel page-fault work

`s = s + "ab"` repeated. Simple 40k iterations = **55,962 ms**; Python = **461
ms** (even a genuinely-quadratic Python prepend is 210 ms). **121x slower.**

Scaling confirms O(n^2): 20k=15.9 s, 40k=56.0 s (3.5x for 2x n).

The cost is **not** interpretation and **not** the copy. `/usr/bin/time -v` on
the 20k case:

- User time **0.57 s**, System time **8.98 s** — 94% of CPU is in the kernel.
- Minor page faults **107,792** (control: 2,159).
- Max RSS **447 MB** — to build a **40 KB** string.

The concat code itself is optimal: `concat_text`
(`src/compiler_rust/compiler/src/interpreter/expr/ops.rs:99`) does one
`String::with_capacity` + two `push_str`, and `Value::text`
(`src/compiler_rust/compiler/src/value.rs:1624`) is just `Arc::new`. The hot arm
is `ops.rs:735`.

**Mechanism: RSS tracks the *sum of every allocation ever made*, so freed
buffers are never reused.**

| iters | total bytes allocated | max RSS | minor faults |
|---|---|---|---|
| 5,000 | 25 MB | 66 MB | 1,390 |
| 10,000 | 100 MB | 148 MB | 3,973 |
| 20,000 | 400 MB | 459 MB | 86,339 |

Each iteration allocates a buffer exactly 2 bytes larger than the last, so a
freed block of size k can never satisfy the next request of size k+2. This
defeats mimalloc's size-class reuse: the heap grows monotonically, pages are
committed/purged, and the process pays ~100k minor faults. mimalloc tuning only
dents it (`MIMALLOC_RESET_DELAY=-1`: 15.9 s -> 11.1 s), confirming the problem
is the allocation *pattern*, not the purge policy.

**Fix direction (not yet implemented):** grow in place when the left operand's
`Arc<String>` is uniquely referenced — CPython's `str +=` optimization. The
obstacle is that the environment slot for `s` still holds a reference while
`s + "ab"` is evaluated, so the refcount is 2 and `Arc::make_mut` would clone
anyway; making this work needs the assignment path to release the old binding
before the concat commits. This is real interpreter surgery on the binary every
lane depends on, so it is filed rather than patched speculatively.

## Where the 5 s/file actually is

The seed compiles a hello-world in **198 ms**, and per-op interpreter cost is
~100-260 ns. At that rate 5 s/file implies ~20-30M interpreted ops per file.
The lever is therefore either (a) the self-hosted compiler's algorithmic op
count (a separate agent is profiling the self-hosted parser), or (b) widening
JIT coverage so compiler code stops hitting `FallbackReason`. It is **not** raw
interpreter dispatch cost.

## Status

No code fix shipped. No shape met the ">5x slower than Python ⇒ fix it" bar
except string concat, whose fix is scoped above and deliberately deferred as
too risky to land without full validation. Benchmarks:
`scratchpad/thru/{a,b,c,d,e1,e2,f,g,h}.spl`.
