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

## The one real defect: repeated string append is quadratic

### Corrected measurement (supersedes the first pass)

The first pass measured 20k appends at 15.9 s and 40k at 56.0 s. Those numbers
were **load-contaminated** (box load 46 at the time) and are retained here only
so the correction is auditable. Re-measured back-to-back against Python,
min-of-3, at load ~28:

| appends | seed | python | ratio |
|---|---|---|---|
| 10,000 | 191 ms | 37 ms | 5x |
| 20,000 | 660 ms | 56 ms | 11x |
| 40,000 | 12,114 ms | 128 ms | **94x** |

The defect is real and is worse than quadratic at the top end: 10k->20k costs
3.5x, but 20k->40k costs **18x**. The knee is the point where the process starts
paying page faults for buffers it can never reuse — at 40k appends RSS reaches
~1.7 GB to build an 80 KB string, and 94% of CPU is kernel time.

Mechanism: each append allocates a buffer exactly 2 bytes larger than the last,
so a freed block can never satisfy the next request. The heap grows
monotonically and mimalloc's size-class reuse is defeated. RSS tracks the *sum
of every allocation ever made*:

| iters | total bytes allocated | max RSS |
|---|---|---|
| 5,000 | 25 MB | 66 MB |
| 10,000 | 100 MB | 148 MB |
| 20,000 | 400 MB | 459 MB |

mimalloc tuning only dents it (`MIMALLOC_RESET_DELAY=-1`: 15.9 s -> 11.1 s),
confirming the problem is the allocation *pattern*, not the purge policy.

### There are two engines, and the defect lives in both

`bin/simple run` defaults to **JIT**, not the tree-walk interpreter
(`driver/src/exec_core.rs:195` `ExecutionMode::Jit`; dispatch
`driver/src/cli/basic.rs:499` -> `exec_core.rs:912` -> `run_file_jit`
`exec_core.rs:993`). `SIMPLE_EXECUTION_MODE=interpret` selects the AST
interpreter. Both lanes had the same quadratic defect, in different code.

**JIT lane (default, still OPEN).** MIR lowers `s + "ab"` to a call to
`rt_string_concat` (`compiler/src/mir/lower/lowering_expr_ops.rs:363-393`),
implemented at `runtime/src/value/collections.rs:2407`. It does **three O(n)
passes per append**: allocate exactly `len_a+len_b` with zero slack, copy both
sides, then re-hash the entire string with fnv1a. Nothing is amortized.

A complete incremental **StringBuilder already exists** —
`rt_string_builder_new/push/finish/len/free`
(`runtime/src/value/string_builder.rs`), re-exported at `runtime/src/lib.rs:869`
with the comment naming the earlier bug `rt_string_concat_quadratic_2026-06-12`
("O(1) amortized push instead of O(n^2) acc = acc + piece accumulation"). It is
declared to codegen (`compiler/src/codegen/runtime_sffi.rs:405`,
`common_backend.rs:593-597`) — **and MIR never emits it.** Every compiler-side
reference is codegen plumbing or a unit test; no lowering site converts an
accumulator append into builder calls. The fix was built and left wired to
nothing, the same pattern CLAUDE.md documents for `interface_digest_of`.

Fixing the JIT lane properly needs one of:
- a MIR/HIR pass that recognises an accumulator-append loop and lowers it to
  `rt_string_builder_*` (safe by liveness: the old value is provably dead), or
- refcounting heap strings so `rt_string_concat` can grow in place when the left
  operand is uniquely owned.

Neither is a minimal patch. Heap strings are a flat inline-data allocation
(`RuntimeString { header, len, hash, data.. }`, `alloc_runtime_string`
`collections.rs:301`) with **no refcount**, and Simple strings are documented
immutable, so in-place mutation is unsound without one of the above. Filed, not
patched speculatively.

**Interpreter lane (FIXED, this change).** `try_string_append_in_place`
(`compiler/src/interpreter/node_exec.rs`) already existed as the designated fast
path for `s = s + x` and `s += x`, and correctly took the binding out of the
environment with `env.remove(name)` — but then did `s.as_ref().clone()`
**unconditionally**, deep-copying the whole string on every append. It was a
fast path in name only, and the loop stayed quadratic.

Fix: `Arc::try_unwrap(s).unwrap_or_else(|shared| shared.as_ref().clone())`.
Because `env.remove` already dropped the environment's reference, the strong
count is 1 whenever this variable is the sole holder, so `try_unwrap` returns
the owned `String` and `push_str` grows its existing buffer with `String`'s
amortized doubling. The aliased case is unchanged — another holder makes
`try_unwrap` fail and we copy exactly as before, preserving value semantics.

Measured on the interpreter lane (`SIMPLE_EXECUTION_MODE=interpret`), pre vs
post, same binary build:

| appends | pre | post | speedup |
|---|---|---|---|
| 5,000 | 72 ms | 48 ms | 1.5x |
| 10,000 | 156 ms | 53 ms | 2.9x |
| 20,000 | 177 ms | 64 ms | 2.8x |
| 40,000 | 0.28 s | 0.16 s | 1.8x |
| 80,000 | 0.96 s | 0.29 s | **3.3x** |

The asymptotics change, which is the real result: pre-fix cost multiplies by
**3.4x** per doubling of N (quadratic); post-fix by **1.8x** (linear).

Mechanism test: `string_append_in_place_tests` in the same file counts the
number of DISTINCT string data pointers across 20,000 appends — deterministic,
no timing, so it is stable on a loaded box. Post-fix that is O(log N) (amortized
doubling); pre-fix it is O(N). Verified to fail pre-fix (**3585** distinct
buffers, over the 1000 bound) and pass post-fix. A second test pins that an
aliased string is still never mutated in place.

## Where the 5 s/file actually is

The seed compiles a hello-world in **198 ms**, and per-op interpreter cost is
~100-260 ns. At that rate 5 s/file implies ~20-30M interpreted ops per file.
The lever is therefore either (a) the self-hosted compiler's algorithmic op
count (a separate agent is profiling the self-hosted parser), or (b) widening
JIT coverage so compiler code stops hitting `FallbackReason`. It is **not** raw
interpreter dispatch cost.

## Status

- Interpreter lane: **FIXED** (quadratic -> linear, pinned by a deterministic
  allocation-count test that fails pre-fix).
- JIT lane (the default for `bin/simple run`): **OPEN**. Root cause located
  exactly (`rt_string_concat`, no amortization, plus an unwired StringBuilder
  that was written for this very bug). Deliberately not patched: a correct fix
  needs a MIR lowering pass or heap-string refcounting, neither of which is a
  minimal change to the binary every lane depends on.
- No other shape met the ">5x slower than Python ⇒ fix it" bar.

Because `run` defaults to JIT, this change does **not** move the `simple run`
concat benchmark — that number only improves when the JIT lane is fixed.

---

## JIT lane: FIXED (2026-08-21)

Two changes, in the order they were made.

### 1. Runtime — lazy string hashing

`RuntimeString.hash` was computed eagerly at every construction site, so
`rt_string_concat` re-hashed the ENTIRE result on every append: the accumulation
was quadratic in HASH work on top of the quadratic copy. The field has exactly
one reader in the tree (`value_hash()` in `value/sffi/equality.rs`, reached only
when a string is a dict/set key), so every other string paid for nothing. All
construction paths now store `STRING_HASH_UNCOMPUTED` (`0`, which doubles as the
empty string's hash) and `runtime_string_hash()` computes and memoises on first
key use.

This also fixed a latent hash-consistency bug: `rt_string_new_with_len_hash`
(used by file reads) stored `len` in the hash field instead of the FNV-1a value
every other path stored, so a string read from a file and an equal literal
hashed differently.

Pinned by deterministic counts (a `cfg(test)` counter inside `fnv1a_hash`), in
`value::collections::lazy_string_hash_tests`: 20k appends perform **0** hash
walks; first key use performs exactly 1; a second use performs 0; equal strings
built three different ways hash equally.

### 2. MIR — emit the string builder for the accumulation pattern

New pass `src/compiler_rust/compiler/src/mir/string_accum.rs`, run at the end of
`MirLowerer::lower_module` (the single choke point every backend goes through,
so JIT and native cannot diverge). It finds a natural loop containing exactly
one `s = s + <expr>` on a local, and rewrites it to `rt_string_builder_new` +
seed push in the preheader, one `rt_string_builder_push` per iteration, and
`rt_string_builder_finish` + store-back on every exit edge (edges are split, so
an exit target shared with non-loop paths is safe). The builder already existed
from bug `rt_string_concat_quadratic_2026-06-12` and was already declared to
codegen; nothing had ever emitted it.

The match rules are conservative and documented at the top of that file: left
operand only (a prepend is not this pattern), exactly one read and one write of
the local in the loop, no other consumer of the local's address, no
closure/interp/asm/indirect call in the loop, no in-loop return, and a single
preheader. `SIMPLE_NO_STRING_BUILDER=1` disables the pass.

Two bugs found by running it end to end, both of which produced silently WRONG
strings rather than crashes, and both now pinned by tests:

* `LocalAddr.local_index` is not an index into `func.locals` — it is a position
  in the combined `[implicit][params][locals]` space whose implicit COUNT is
  itself inferred from the max index used. Taking an index above every existing
  one grew that count and shifted the meaning of every other index: the
  accumulator was then read as the `i32` parameter's slot and its pointer was
  `ireduce`d to 32 bits (`<invalid-heap:0x72021711>`).
* Inserting the push at the removed `Load`'s index put it before its own operand
  (`ConstString`) was defined; the JIT read a stale `vreg_values` entry from the
  previous iteration and every result came out exactly one push short.

### Measured, `bin/simple run` (JIT), `s = s + "abcdefghij"`

| appends | pre | post |
|---|---|---|
| 10,000 | 4.4 s | 0.10 s |
| 20,000 | 30.1 s | 0.07 s |
| 40,000 | 99.1 s | 0.18 s |
| 80,000 | OOM-killed at 24 GB RSS after 259 s | 0.16 s |

Post is flat because it is now dominated by process start and JIT compilation;
the quadratic term is gone. Python's 0.13 s for 40k is no longer the benchmark
to beat.

### Verification

* `cargo test -p simple-compiler --release --lib`: 3738 passed / 52 failed —
  the same 52 as the recorded baseline, no new failures.
* `cargo test -p simple-runtime --release --lib`: 1180 passed / 10 failed — the
  same 10 fail at the parent commit, verified by building and running the
  baseline in a separate worktree.
* Engine-differential corpus (`test/fixtures/engine_differential/`), JIT vs
  interpreter with the same binary: 9 match / 2 differ, byte-identical to the
  pre-change binary's result (`i64_boundary_values`, `utf8_slice_boundary` are
  pre-existing and unrelated).
* New fixture `test/fixtures/engine_differential/string_accumulation_loop.spl`
  covers zero iterations, a non-empty seed, an empty seed, a 2000-append run, a
  mid-loop read (must NOT be rewritten), a prepend (must NOT be rewritten), and
  non-ASCII content. JIT and interpreter agree on every line.

Status: JIT lane **FIXED**.
