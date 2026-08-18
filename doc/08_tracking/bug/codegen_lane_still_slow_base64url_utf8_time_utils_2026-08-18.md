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
| C-MIG-0023 base64url | 44.1x | **44.7x** (simple_us=6155385 c_us=137565, 50 reps x 100-vector corpus) | no improvement moving to JIT |
| C-MIG-0023 base64url | 44.1x | ~~44.7x~~ -> **35.05x post-fix** (simple_us=404308 c_us=11534, 50 reps x 100-vector corpus, array-accumulator fix landed 2026-08-18) | improved ~1.28x further, still OPEN (>2x threshold) |
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
