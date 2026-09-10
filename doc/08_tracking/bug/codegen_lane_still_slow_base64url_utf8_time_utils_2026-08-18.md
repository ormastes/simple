# Codegen (JIT) lane still >2x C oracle for C-MIG-0019/0022/0023

**Date:** 2026-08-18
**Status:** OPEN — perf finding, no fix attempted here
**Binary used:** `bin/release/x86_64-unknown-linux-gnu/simple` (Rust bootstrap
seed — printed `WARNING: this Rust-built Simple binary is a bootstrap seed
only`), 59620392 bytes, mtime 2026-08-18 01:08:42. `readlink -f bin/simple`
resolved to this path at measurement time.

## Context

`doc/08_tracking/c_migration/c_migration_inventory.sdn` entries C-MIG-0019,
C-MIG-0022, C-MIG-0023 recorded interpreter-lane (`bin/simple test`) PERF
findings. Per `.claude/rules/testing.md` ("run and test are DIFFERENT
ENGINES"), the interpreter lane is not the engine ordinary programs run on;
this doc records the follow-up codegen-lane (`bin/simple run` +
`SIMPLE_JIT_STRICT=1`, Cranelift JIT, strict mode refuses execution rather
than silently falling back to interpreter) re-measurement, run on three new
throwaway harnesses (not committed — scratch dir):
`bench_base64url_codegen.spl`, `bench_utf8_validate_codegen.spl`,
`bench_time_utils_codegen.spl`. Each harness asserts the shared-corpus KAT
match (Simple output == C oracle output) before any timing loop, so none of
these ratios are timing incorrect output. All three ran to completion under
`SIMPLE_JIT_STRICT=1` with exit 0 — no strict-mode refusal, so the codegen
lane numbers below are valid measurements, not interpreter numbers in
disguise.

## Findings — still above the plan's 2x PERF-finding threshold

| finding | interpreter ratio | codegen ratio | verdict |
|---|---|---|---|
| C-MIG-0023 base64url | 44.1x | ~~44.7x~~ -> ~~35.05x post-fix~~ -> **PINNED-CORPUS A/B (2026-08-18): pre-fix 438.11x -> post-fix 32.25x** (see corrected table below) | improved ~13.6x further on a pinned corpus, still OPEN (>2x threshold) |
| C-MIG-0022 utf8_validate | 32.9x | ~~16.6x~~ -> **8.27x post-fix** (simple_us=140011 c_us=16938, 300 reps x 88-vector corpus, batched-ASCII fast path added 2026-08-18) | improved ~2x further, still OPEN (>2x threshold) |
| C-MIG-0019 time_utils | 2.01x | **3.18x** (simple_us=265627 c_us=83431, 30 reps x 100-vector corpus) | ARTIFACT — isolated 2026-08-18: probe-free batch timing shows codegen ~1.6x FASTER than interpreter, see finding 3 verdict |

## Specific hot constructs (for whoever picks this up)

1. **C-MIG-0023 base64url/base64 — scalar `text + text` concatenation in a
   loop.** `src/lib/common/base_encoding/base64.spl:49` (`base64_encode`)
   builds `out` via `out = out + <char>` inside a `while` loop over every
   input byte (3 output chars per 3 input bytes), and
   `base64url_encode` (`base64.spl:184`) does a SECOND full `out = out + c`
   pass over the standard-base64 string just to remap `+`/`/`/`=`. That is
   two O(n) scalar string-rebuild passes per call, each `+` plausibly
   reallocating/copying the growing `text` value. This construct does not
   appear to get any cheaper under the Cranelift JIT (44.1x interpreter ->
   44.7x JIT, i.e. flat) — suggests `text + text` concatenation cost is
   dominated by the runtime string representation/allocation, not by
   interpreter dispatch overhead, so JIT-ing the surrounding loop control
   flow does not help. A fix would replace the accumulate-by-concatenation
   pattern with a pre-sized mutable byte buffer written once and converted to
   `text` at the end (mirroring the C oracle's single-pass table lookup into
   a fixed output buffer).

   **Fix landed 2026-08-18:** `base64_encode`/`base64url_encode`/
   `base64url_decode`/`_bytes_to_text`
   (`src/lib/common/base_encoding/base64.spl`) rewritten to accumulate into a
   `[u8]` (or `[text]` for the UTF-8 decode side) array via `.push()` and
   join/convert to text ONCE at the end, instead of `out = out + c` per
   iteration. Codegen ratio improved 44.7x -> 35.05x (simple_us=6155385 ->
   404308, ~15x absolute reduction; c_us also shifted 137565 -> 11534 between
   runs — machine-load noise on this shared box, not attributable to the
   fix). Still >2x — remains OPEN; remaining gap is per-byte function-call/

   **PINNED-CORPUS A/B, corrected 2026-08-18 (this measurement):** the ratio
   above compared two DIFFERENT runs' corpora (pre-fix used lengths 0..99,
   c_us=137565; post-fix used a different run, c_us=11534 — a 12x c_us swing
   between "before" and "after" that a code review correctly flagged as not
   apples-to-apples). Re-measured with ONE harness on ONE pinned corpus so
   pre-fix and post-fix are directly comparable:

   | run | corpus | reps | binary | simple_us | c_us | ratio |
   |---|---|---|---|---|---|---|
   | pre-fix (`31e0eaa099c~1` base64.spl, temporarily swapped in) | 100 seeded inputs, lengths 0..2000 (LCG), printable-ASCII LCG bytes | 50 | `bin/release/x86_64-unknown-linux-gnu/simple`, 59620392 bytes, mtime 2026-08-18 01:08:42 | 294480660 | 672161 | **438.11x** |
   | post-fix (current `src/lib/common/base_encoding/base64.spl`) | same corpus | 50 | same binary | 14477883 | 448885 | **32.25x** |

   Harness: `bench_base64_ab.spl` (scratchpad, not committed) — generates the
   corpus once via an LCG (deterministic, reproducible), asserts encode match
   AND decode round-trip (KAT) against `rt_base64url_encode`/
   `rt_base64url_decode` before any timing, then times `base64url_encode` +
   `base64url_decode` vs. the `rt_` oracle over 50 reps x 100 vectors. Both
   runs used `SIMPLE_JIT_STRICT=1 bin/simple run`, exited 0 (no strict-mode
   refusal), and printed `KAT OK: 100/100 vectors match (encode+decode)`
   before timing. The pre-fix base64.spl was materialized via `git show
   31e0eaa099c~1:src/lib/common/base_encoding/base64.spl`, copied over the
   lib file for the pre-fix run only, then restored with `git checkout --
   src/lib/common/base_encoding/base64.spl`; `git diff --stat` confirmed a
   clean tree afterward.

   **Corrected verdict:** the fix's real improvement on a pinned corpus is
   **~13.6x** (438.11x -> 32.25x), materially larger than the previously
   reported ~1.28x (44.7x -> 35.05x), because the old comparison's differing
   c_us baselines (137565 vs 11534, a 12x swing attributed to "machine-load
   noise") diluted the apparent gain. Still >2x the C oracle — remains OPEN.
   The gap is per-byte function-call/
   array-push/text-conversion overhead vs. the C table-lookup-into-fixed-
   buffer approach, same residual-cost shape as finding 2 below. Along the
   way, found and worked around a genuine JIT correctness bug (not this
   finding's algorithm, a compiler defect): a **module-level** `val [u8]`
   array, indexed and then `.push()`-ed into another `[u8]` array, reads back
   corrupted under the codegen/JIT lane (byte 65 'A' read back as 8); a
   function-local array of the identical bytes does not corrupt. Filed
   separately:
   `doc/08_tracking/bug/jit_module_level_u8_array_index_push_corruption_2026-08-18.md`.
   Full evidence: `doc/08_tracking/c_migration/c_migration_inventory.sdn`
   C-MIG-0023 `perf_codegen` field, POST-FIX paragraph.

2. **C-MIG-0022 utf8_validate — per-byte scalar branch tree, no SIMD.**
   `src/lib/common/base_encoding/utilities.spl:84`
   (`validated_utf8_bytes_to_text_linear`) walks the byte array one byte at a
   time with a cascade of `if`/`elif` range checks per byte
   (`utilities.spl:91-114` and following, continuation-byte/overlong/surrogate
   checks for the 2/3/4-byte cases). The C oracle
   (`src/runtime/runtime_simd_utf8.c`) is SIMD-dispatched
   (SSE2/AVX2/NEON), validating 16-32 bytes per instruction batch on the
   ASCII fast path; the Simple side has no batched-ASCII fast path at all,
   so every byte pays the full branch cascade even for plain ASCII input.
   JIT-ing the branch cascade helped (32.9x -> 16.6x) but the algorithmic gap
   (no batching) remains the dominant cost. A fix would add an 8-byte-at-a-
   time all-ASCII fast-path check (e.g. `& 0x8080808080808080` across a
   `u64`-cast window) before falling back to the byte-by-byte cascade for
   any window containing a high bit.

   **Partial fix landed 2026-08-18:** added an inner tight `while` loop that
   advances through a run of plain-ASCII bytes with a single comparison per
   byte, skipping the full leading-byte elif cascade until a high byte is
   seen (`utilities.spl:84`, byte-for-byte identical multibyte semantics).
   This is a per-byte scalar batching win, not real SIMD word-at-a-time
   batching — codegen ratio improved 16.6x -> 8.27x (300 reps x 88-vector
   corpus, KAT-verified, same binary as above). Still >2x — remains OPEN;
   the `u64`-window all-ASCII check described above is the next step to
   close the rest of the gap.

3. **C-MIG-0019 time_utils — per-call arithmetic overhead dominates at this
   scale, and JIT made it relatively worse.** `std.common.time_utils`
   implements the Howard-Hinnant era-based civil-calendar algorithm (divmod-
   heavy integer arithmetic, no loops, no string building) in
   `timestamp_from_components`/`timestamp_add_days`/`timestamp_diff_days`.
   Because there is no loop or allocation to speed up, `SIMPLE_JIT_STRICT=1`
   moving the ratio from 2.01x (interpreter) to 3.18x (JIT) is suspicious:
   it suggests either (a) call-overhead/boxing cost between the JIT-compiled
   caller and the extern-dispatched C oracle call did not shrink
   proportionally to the arithmetic itself getting faster under JIT (i.e. the
   *oracle* call path got relatively cheaper too, widening the ratio), or
   (b) i32/i64 conversion or the harness's own per-call `time_now_unix_micros`
   probe overhead is a larger fraction of the (now much shorter) simple-side
   wall time. This needs isolation — a version of the harness that batches N
   calls between clock reads, rather than reading the clock around every
   individual `timestamp_from_components`/`add_days`/`diff_days` call,
   would separate real arithmetic cost from clock-read/call overhead. Filed
   here rather than fixed; not attempted in this pass.

   **VERDICT (isolated 2026-08-18): ARTIFACT — not a real codegen
   regression.** Same binary as above (`bin/release/x86_64-unknown-linux-gnu/simple`,
   Rust bootstrap seed, mtime 2026-08-18 01:08:42, size 59620392 bytes).
   Three throwaway KAT-guarded harnesses in the scratch dir
   (`bench_probe_overhead.spl`, `bench_time_utils_batch.spl`,
   `bench_time_utils_percall.spl`), each run once under plain interpret
   (`bin/simple run`) and once under `SIMPLE_JIT_STRICT=1` (exit 0, no
   strict-mode refusal, so both are real codegen-lane runs). KAT: epoch
   round-trip (`timestamp_from_components(1970,1,1,...) == 0`,
   `timestamp_add_days`/`timestamp_diff_days` self-consistent), verified
   before timing in every harness. `time_utils` uses no arrays (confirmed
   by reading `src/lib/common/time_utils.spl:153-181` — plain `i64`
   scalar arithmetic only), so the module-val-array JIT hazard flagged in
   the task brief does not apply here.

   - **Hypothesis 1 (bare clock-probe cost), N=10000 back-to-back
     `time_now_unix_micros()` pairs:** interp 0.033us/call, codegen
     0.045us/call. Codegen's own probe call is ~1.36x costlier than
     interpreter's, but both are far under 0.1us — this alone cannot
     explain a 265627us/83431us=3.18x split over only 3000 calls
     (~88.5us/call implied in the original run), so probe cost in
     isolation is not the whole story.
   - **Hypothesis 2 (batch timing, clock read only once around a
     10000-iteration loop of `from_components`+`add_days`+`diff_days`):**
     interp 950us total (0.095us/iter), codegen 599us total
     (0.0599us/iter). With clock probes removed from the hot path,
     **codegen is ~1.59x FASTER than interpreter**, the opposite
     direction from the original finding.
   - **Hypothesis 3 (per-call-probe replica of the original harness
     shape — 3 probe pairs per iteration, same 3 functions, N=3000):**
     interp 534us total (0.0593us/call), codegen 334us total
     (0.0371us/call). Again codegen is faster (~1.6x), not slower.

   **Corrected reading:** none of the three isolations reproduce "JIT
   made time_utils relatively worse." `time_utils` has no loop or
   allocation, so its true per-call cost is tens of nanoseconds — the
   same order of magnitude as a `time_now_unix_micros()` syscall/vDSO
   read itself. At that scale the *ratio* against the C oracle is
   dominated by clock-probe placement and by scheduler/syscall noise on
   a shared, loaded box, not by any genuine codegen-vs-interpreter
   difference in the arithmetic. The original per-call-probe methodology
   (clock read wrapped around every individual function call) is
   unreliable for functions this cheap; base64url/utf8_validate are
   unaffected because their absolute per-call cost (loop-bearing, many
   microseconds) swamps probe overhead by orders of magnitude, which is
   why only the loop-free time_utils entry shows this artifact. **No
   compiler or library fix is indicated by this data** — the C-MIG-0019
   codegen "regression" should be treated as a debunked measurement
   artifact, not an open perf regression.

## Non-actions taken here

No compiler source change was made. This is a measurement + bug-filing pass
only, per the task's explicit constraint not to fix the compiler.

## Addendum 2026-08-18: C-MIG-0029/0030 sqrt_f64/cbrt_f64 — algorithmic fix applied, interpreter-tax gap remains

Separate from the time_utils/base64url/utf8 investigation above, but same
family (a >2x ratio against the C/Rust oracle that survives after the known
fixable cause is addressed). `sqrt_f64` (special.spl `_sqrt_f64`, C-MIG-0029)
and `cbrt_f64` (cbrt.spl `_cbrt_pos`, C-MIG-0030) were fixed-iteration-count
(40 / 80) Newton loops with a poor initial guess — a genuine algorithmic
defect, not an interpreter tax. Both were rewritten to: (1) range-reduce the
input into a bounded window ([1,4) for sqrt via divide/multiply-by-4, [1,8)
for cbrt via divide/multiply-by-8, tracking the reduction count, then scaling
the reduced root back by 2^count), giving a bounded-ratio starting guess for
every input magnitude, and (2) a relative-epsilon convergence test
(`|delta| <= 1e-15 * |result|`) capped at 8 iterations instead of a fixed
40/80.

Results (100-vector shared bulk corpus, `bin/simple test`, tree-walk
interpreter, single run each):

| kernel | before | after | old ratio | new ratio |
|---|---|---|---|---|
| sqrt_f64 | simple_us=8109 c_us=457 | simple_us=5969 c_us=488 | ~17.7x | ~12.2x |
| cbrt_f64 | simple_us=17390 c_us=498 | simple_us=6320 c_us=467 | ~34.9x | ~13.5x |

Both crosslang differential specs stay green (`cbrt_crosslang_spec.spl`:
7 examples, 0 failures; `special_sqrt_crosslang_spec.spl`: 8 examples, 0
failures), with new stress cases added for 1e300/1e-300 magnitudes and
values straddling the reduction window boundary (0.999999/1.000001) to
exercise the new range-reduction path specifically.

**Remaining gap, stated plainly:** both ratios are still >2x. The iteration
count is no longer the driver — it dropped from a fixed 40/80 to a
data-dependent 1-8 (typically 5-6 to converge from the bounded-ratio start).
The residual ~12-13x is dominated by per-iteration/per-call interpreter
dispatch overhead (the same tree-walk-interpreter tax documented throughout
this file for other kernels), not by a further algorithmic defect in either
kernel. Closing it further requires the JIT/native codegen lane, not another
algorithm change to these two functions. C-MIG-0029/0030 registry entries
updated in `doc/08_tracking/c_migration/c_migration_inventory.sdn` with both
before/after measurements.

## Addendum 2026-08-18 (goal 3 closure): C-MIG-0029/0030 codegen-lane verdict — JIT helps ~2.5x but does NOT close the gap

**Binary:** `bin/release/x86_64-unknown-linux-gnu/simple`, 59673480 bytes,
mtime 2026-08-18 06:12:48 (`readlink -f bin/simple` resolved to this path at
measurement time, unchanged across the whole session).

**Method correction, load-bearing for this addendum:** `SIMPLE_JIT_STRICT=1
bin/simple run` is NOT an interpreter-vs-codegen A/B — bare `bin/simple run`
already Cranelift-JITs by default (`.claude/rules/testing.md`: "`bin/simple
run` uses the Cranelift JIT; `bin/simple test` hard-defaults to the tree-walk
interpreter"). Confirmed directly: running the harnesses below with and
without `SIMPLE_JIT_STRICT=1` under `bin/simple run` produced byte-identical
timing (ratio 61.9x both times) — `SIMPLE_JIT_STRICT=1` only changes refusal
behavior on a JIT failure, it does not select an engine. The actual knob is
`SIMPLE_EXECUTION_MODE=interpreter|jit`, used for all numbers below.

**Harnesses:** `bench_sqrt_f64_codegen.spl` / `bench_cbrt_f64_codegen.spl`
(scratchpad, not committed). Each asserts 3 KATs first (perfect
cube/square, an oracle-tolerance check at x=2.0, and one at x=1e300), then a
pinned 100-vector seeded corpus (LCG-generated exponent in [-300,300] x
mantissa in [1,10), plus exact-power/boundary cases: 0.0, 1.0, 4.0/8.0, 9.0,
16.0, 1e-300, 1e300, 0.999999, 1.000001, 1e6) verified in full against the
`rt_math_sqrt`/`rt_math_cbrt` oracle before any timing. Both harnesses printed
`KAT OK: 100/100 vectors match` under both engines. 200 reps x 100 vectors;
one clock pair around the whole double loop (batch-timed) plus a
per-call-probe variant (clock read around every individual call) run
separately, to make probe distortion visible per the time_utils finding above.

**JIT correctness pitfall found while writing the cbrt harness (worked
around, not filed separately — did not block this measurement):**
`if not _approx(f(x), g(x), tol):` with two function-call results passed
directly as nested call arguments returned a wrong boolean under
`SIMPLE_EXECUTION_MODE=jit` (a false KAT failure on values that printed
identically when read back separately); binding each call to a `val` first
and passing the locals fixed it. Anyone writing a similar codegen-lane
harness should bind call results to locals before passing them into a
boolean-returning helper.

**2x2 results (batch-timed vs. per-call-probe, interpreter vs. JIT):**

| function | interpreter batch | interpreter probe | JIT batch | JIT probe |
|---|---|---|---|---|
| sqrt_f64 | simple_us=9230087 c_us=59705 **ratio=154.6x** | simple_us=9241880 c_us=86453 **ratio=106.9x** | simple_us=35653 c_us=577 **ratio=61.8x** | simple_us=36639 c_us=1018 **ratio=36.0x** |
| cbrt_f64 | simple_us=6688979 c_us=62860 **ratio=106.4x** | simple_us=6711533 c_us=89511 **ratio=75.0x** | simple_us=24911 c_us=940 **ratio=26.5x** | simple_us=24832 c_us=1460 **ratio=17.0x** |

(The batch-timed absolute interpreter/JIT wall times above are the more
reliable evidence for the engine speedup claim; the oracle's `c_us` itself is
only tens-of-microseconds to low-hundreds-of-microseconds over 20,000 calls
— genuinely cheap hardware/library calls — so both batch and probe ratios
against it are noisy in the same direction as the time_utils finding, though
nowhere near enough to explain an over-60x gap.)

**Verdict: the task's premise is half right and half wrong.** JIT genuinely
helps — Simple-side wall time drops ~2.5x for both functions (sqrt:
9.23M us -> 35.7K us; cbrt: 6.69M us -> 24.9K us), and the oracle ratio
improves correspondingly (sqrt 154.6x -> 61.8x; cbrt 106.4x -> 26.5x), so the
residual IS partly interpreter dispatch tax, exactly as hypothesized. But
codegen does NOT bring either function anywhere near the plan's <=2x
threshold: **sqrt_f64 remains OPEN at 61.8x (batch) / 36.0x (probe) under
JIT**, and **cbrt_f64 remains OPEN at 26.5x (batch) / 17.0x (probe) under
JIT**. Neither is RESOLVED. The claim "the codegen lane should be materially
better" is confirmed directionally (both ~2.5x-4x better than interpreter
depending on which pairing you compare) but not in magnitude — a Newton-
iteration kernel doing several f64 arithmetic ops per iteration, 1-8
iterations per call, plus Simple's function-call/argument-marshalling
overhead, still cannot approach a single hardware sqrt/cbrt instruction's
cost even fully JIT-compiled. Closing the remaining gap would require either
inlining the kernel more aggressively at the JIT level or accepting that a
software Newton fallback can never match a hardware FP instruction within 2x
for this shape of workload. C-MIG-0029/0030 registry entries updated with
`perf_codegen` fields recording this verdict in full.

## RE-MEASURED + PARTIALLY FIXED 2026-09-06 (aarch64): base64url 420x -> 17.6x

**Host/binary.** aarch64 Linux, 20 CPUs, shared and loaded (a full bootstrap
plus three other agent sessions running concurrently — treat absolute
microseconds as an envelope, but every A/B below is same-host, same-corpus,
same-session). Baseline binary: the Rust bootstrap seed at
`bin/release/aarch64-unknown-linux-gnu/simple`, 50,093,192 bytes, sha256
prefix `3d120a6f9ab5704b`. Fixed binary: same tree plus the runtime changes
below, 51,104,760 bytes. Both print the `bootstrap seed only` banner. All
runs under `SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1 bin/simple run`,
exit 0, no strict-mode refusal — real codegen-lane numbers, and a silent
interpreter fallback is impossible.

**Harnesses** (scratchpad, not committed): `bench_b64_codegen.spl`,
`bench_utf8_codegen.spl`, `bench_crc32_codegen.spl`, plus the attribution
probes `probe_stages.spl`, `probe_stages2.spl`, `probe_scaling.spl`,
`probe_join_correct.spl`. Every timing harness asserts its KAT against the C
oracle BEFORE timing and aborts on mismatch; base64url's prints
`KAT OK: 100/100 vectors match (encode+decode)` on a pinned 100-vector LCG
corpus (lengths 0..2000, printable ASCII), and the utf8 one prints
`KAT OK: 88/88 vectors agree with the C oracle`.

### Where the time actually went — NOT where this record guessed

`perf`/attach profiling is unavailable here (`perf_event_paranoid=4`,
`ptrace_scope=1`), so cost was attributed by timing each stage of the kernel
in isolation over the same 300,000 bytes:

| stage (probe) | ns/byte |
|---|---|
| pre-sized `[u8]` indexed store (`out[i] = src[i]`) | 3 |
| `[u8]` growth, `out = out.push(b)` (reassigned) | 2 |
| `[u8]` growth, `out.push(b)` (bare) | 2 |
| `s.bytes()` | <1 |
| **`[text]` accumulate + `join("")` (the `_bytes_to_text` shape)** | **328** |

Two conclusions, both contradicting this record's stated hypotheses:

1. **The generated code is not the defect.** `[u8]` scalar loops run at
   2-3 ns/byte, and `crc32_text` measured 1.23x the C oracle on this host
   (see the sibling crc32 record). The JIT's array/scalar codegen is fine.
2. **`out = out.push(x)` is NOT O(n^2).** Scaling at n = 750/1500/3000 with
   reps fixed gave 273/518/1014 us — dead linear. The "reassigned push
   rebuilds the array" theory that this file and `crc.spl` both repeat is
   wrong for `[u8]`; reassignment is free.

Decomposing the 328 ns/byte at n = 750/1500/3000 (all linear, so these are
per-element CONSTANTS, not quadratic terms):

- `[text]` push: ~47 ns/element (25x the `[u8]` push at ~2 ns)
- **`join("")`: ~237 ns/element** — the single largest term
- `char_from_codepoint` per byte: a fresh 1-char `text` per byte

Root cause, read out of the runtime source rather than guessed:

- `rt_string_join` (`runtime/src/value/collections.rs:4117`) calls
  `rt_value_to_string` on EVERY element. That is
  `value_to_display_string` (a Rust `String` allocation) followed by
  `rt_string_new` (a fresh interned `RuntimeValue`) — two allocations per
  element, performed purely to read back bytes an already-`text` element
  already owned. `.join` dispatches here, not to `rt_array_join`
  (`codegen/instr/calls.rs:3622`, `closures_structs.rs:2157` both map
  `"join" => "rt_string_join"`).
- `rt_bytes_to_text` (`runtime/src/value/sffi/file_io/file_ops.rs:1439`)
  read each byte through a boxed `rt_array_get` — measured ~46 ns/BYTE for
  what should be a memcpy — even though a bulk accessor for the packed `[u8]`
  representation already existed two functions below it (`byte_array_bytes`,
  used by `rt_file_write_bytes_array`).
- `_bytes_to_text` (base64.spl) and `base_encoding_bytes_to_text`
  (utilities.spl) both minted one `text` PER BYTE and then joined or
  concatenated them. This function is on the path of every base64/base64url
  encode AND decode, which is why the gap was symmetric.

### Fix (commit `9e5671ad32d`, branch `work/codegen-text-builtin-per-element-allocs`)

Four files, one root cause (per-element boxed round-trips in bulk text/byte
builtins):

1. `rt_string_join` — an element that is already a heap `String` has its own
   bytes appended directly; non-`String` elements keep the display-formatter
   path verbatim, so `[1,2,3].join(",")` is unaffected.
2. `rt_bytes_to_text` — new `packed_byte_array_bytes` fast path
   (`collections.rs`). A packed `[u8]`'s elements are `u8` by construction,
   so neither of the function's rejections (non-int, out of 0..255) can fire
   for it; skipping the per-element check is behaviour-preserving, not a
   relaxation. Boxed-element arrays keep the checked loop.
3. `_bytes_to_text` (base64.spl) and 4. `base_encoding_bytes_to_text`
   (utilities.spl) — both now accumulate `[u8]` and convert once. Validation
   walks and branch structure are untouched. Equivalence is by construction:
   `join("")` IS the concatenation of the parts' UTF-8 bytes, and for
   `b < 0x80` the part was `char_from_code(b)` = `table[b:b+1]` = exactly
   that one byte. The multibyte branches still call `char_from_codepoint` and
   push ITS bytes, so their deliberately-unvalidated behaviour is preserved
   rather than reinterpreted. As a side effect utilities.spl drops from 5
   in-loop `rt_bytes_to_text` call sites to 1 (net -4 on the direct-`rt_*`
   ratchet in `src`).

### After — same harness, same pinned corpus, same session

| kernel | baseline simple_us | after simple_us | c_us before/after | ratio before -> after |
|---|---|---|---|---|
| base64url (50 reps x 100 vectors) | 5,293,846 | **220,515** | 12,605 / 12,031 | **420x -> 17.6x** (24x faster) |
| crc32_text (500 iters, 2090 B) | 7,030 | 6,819 | 5,691 | 1.23x -> 1.20x (no regression) |
| utf8_validate (300 reps x 88 vectors) | 488,614 | 482,616 | 12,705 / 12,607 | **38x -> 38x (UNCHANGED)** |

Attribution of the base64url win, measured in two steps on this host:
library fix alone, on the UNMODIFIED baseline binary, 5,293,846 -> 1,232,227
(4.3x); adding the two runtime fixes, -> 220,515 (a further 5.6x). Both
halves were needed — the library fix removes the per-byte `text`, and the
runtime fix removes the per-byte boxed read in the one bulk conversion that
replaced it.

**Correctness.** `test/01_unit/lib/common/base_encoding/` reports
`125 total, 120 passed, 5 failed, 5 skipped` **both before and after** — the
5 failures are pre-existing and unrelated (the C oracle
`rt_base64url_decode` rejects `+`/`/` input, which the characterization
example expects it to tolerate; reproduced on the pristine tree with the
pristine binary). Zero new failures, zero fixed. `probe_join_correct.spl`
additionally checks 12 join/bytes cases through the new fast paths
(already-string, mixed separators, empty elements, multibyte, `[i64]` and
`[bool]` join, packed/pre-sized/empty `[u8]`): all pass.

### What remains OPEN

- **base64url is still 17.6x, not <=2x.** The per-byte `text` allocation and
  the per-byte boxed byte read are both gone; what is left is the pure-Simple
  per-byte loop itself (encode is already a pre-sized indexed-store loop at
  ~3 ns/byte) plus `base64url_decode`'s extra full pass (it rewrites `-`/`_`
  to `+`/`/` into a second `[u8]`, then delegates to `base64_decode`, which
  walks the result again, so a decode is 3 passes over the data where the C
  oracle does 1). Collapsing decode to a single pass is the obvious next
  step and needs no runtime change.
- **utf8_validate is ~38x on this host and my fixes did not move it** (0.4%,
  within noise — verified by running the same harness on both binaries). Its
  cost is the per-byte scalar branch cascade, exactly as finding 2 above
  says; it already ends in ONE bulk `rt_bytes_to_text`, so it never paid the
  per-element defect. The `u64`-window all-ASCII check finding 2 prescribes
  is still the right next step. Note this 38x is NOT comparable to the 8.27x
  recorded above: different host, different corpus (88 vectors of length
  0..1044 with a multibyte char every 7th), and a different oracle framing.
- **`rt_array_join` (`collections.rs:5543`) has the same defect in a worse
  form** — it builds its result with a fresh `rt_string_concat` per element,
  i.e. N allocations AND O(n^2) bytes copied. It is NOT on the `.join`
  dispatch path (that is `rt_string_join`) so it was left alone under a
  smallest-diff rule, but any caller reaching it pays the quadratic. Fix it
  the same way when something is shown to use it.
- **`char_from_code` allocates a 1-char `text` via a string slice for every
  ASCII codepoint** (`utf8.spl:376`, `table[code:code+1]`). Any remaining
  per-character text-building loop in the stdlib still pays ~200 ns/char for
  this. The fix applied here (accumulate bytes, convert once) is the pattern
  to copy; a census of other `parts.push(char_*)`-then-`join` loops has not
  been done.
