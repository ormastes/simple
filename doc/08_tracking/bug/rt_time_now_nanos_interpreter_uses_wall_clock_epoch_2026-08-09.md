# `rt_time_now_nanos` returns a BOOT-relative epoch natively and a WALL-CLOCK epoch in the interpreter

**Status:** FIXED — status line corrected 2026-08-17 (it read "OPEN — filed,
deliberately not fixed in-stream", which is stale). The interpreter's
`rt_time_now_nanos` is now `Instant`-backed, matching the native C runtime's
`CLOCK_MONOTONIC`: `src/compiler_rust/compiler/src/interpreter_extern/time.rs:304-306`
(`static BASELINE: OnceLock<Instant>` … `.elapsed().as_nanos()`), with the same
baseline applied at `:340-343`. That file's own doc comment at `:315` records
that it "returned wall-clock nanos here until 2026-08-10". Callers wanting an
absolute wall-clock value are directed to `rt_time_now_unix_micros` (`:319`,
`:326`, `:337`).
**NOT proved:** verified by reading the Rust seed source only; no re-run of the
divergence repro on a freshly built binary.
**Found:** 2026-08-09 — stream G2, while converging `file_read_bytes`
**Severity:** silent ~50-year value divergence across execution engines
**Component:** `src/compiler_rust/compiler/src/interpreter_extern/time.rs` vs the C runtime

## Defect

`rt_time_now_nanos` has multiple implementations that disagree on the **epoch**,
not merely on precision:

| implementation | clock | epoch | magnitude today |
|---|---|---|---|
| `src/runtime/runtime_native.c:9073` (`rt_time_now_ns`, forwarded at :9079) | `CLOCK_MONOTONIC` | since **boot** | ~1e13 |
| `src/runtime/simple_core/core_process.spl:113` | `clock_gettime(1, …)` — `CLOCK_MONOTONIC` | since **boot** | ~1e13 |
| `src/compiler_rust/compiler/src/interpreter_extern/time.rs:300` | `SystemTime::now()` | since **`UNIX_EPOCH`** | ~1.7e18 |
| `src/compiler_rust/runtime/src/value/sffi/time.rs:35` | forwards to the C symbol | since **boot** | ~1e13 |

So the pure-Simple core and all three C runtimes (`runtime.c`,
`runtime_native.c`, `runtime_time.c` — see
`scripts/check/runtime_symbol_lane_divergence_baseline.txt:95`) agree on
`CLOCK_MONOTONIC`, and the **interpreter is the lone divergent one**, returning
wall-clock nanoseconds.

The two values differ by roughly five orders of magnitude — about 50 years.

## Why it is dangerous

A *difference* of two readings is correct within a single engine, which is why
this hides: every duration measurement looks fine. It breaks whenever a value is
used **absolutely** or **crosses engines**:

- a timestamp produced under the interpreter and compared against one produced
  by a native build (cache entries, `.sdn` records, evidence artifacts, spec
  fixtures) is ~50 years apart, so freshness/expiry checks invert;
- a boot-relative value serialized as a wall-clock instant dates to 1970;
- benchmark harnesses that mix an interpreted control against a native subject
  compute nonsense deltas rather than failing loudly.

This is the same engine-divergence family as the other 2026-08-09 findings, and
the same hazard class as `file_read_bytes` (converged in this stream): one name,
several implementations, and the caller cannot tell which one it got.

## Why this is filed, not fixed

`src/runtime/runtime_native.c:9124` carries an explicit in-tree ownership note:

> `NOTE: rt_time_now_ns / rt_time_now_nanos / rt_time_now_micros are left
> absolute here on purpose -- they are separately tracked in
> scripts/check/runtime_symbol_lane_divergence_baseline.txt and are owned by
> another lane; do not "fix" them as a side effect of this one.`

The symbol is baselined in that lane-divergence file, so changing any single
implementation would move a tracked baseline belonging to another stream. The
fix is also larger than it looks: it is a **semantic choice**, not a one-line
edit — the name `now_nanos` does not say which epoch is intended, and both are
legitimately wanted somewhere.

## Suggested fix (for the owning lane)

Do not silently align one side. Split the name, the way `file_read_bytes` /
`file_try_read_bytes` was split, so the epoch is in the signature:

- `rt_time_monotonic_nanos()` — `CLOCK_MONOTONIC`, for durations. Explicitly
  documented as having **no** meaningful absolute value.
- `rt_time_unix_nanos()` — since `UNIX_EPOCH`, for timestamps.

Then make every implementation of each name agree, and retire
`rt_time_now_nanos` rather than leaving an epoch-ambiguous alias. Note that
`rt_time_now_micros` (`runtime_native.c:9083`, `time.rs:315`) has the **same
split** and must be converged in the same change — fixing only the nanos variant
leaves the identical defect one function over.

## Oracle

Print `rt_time_now_nanos()` from the same `.spl` source under the interpreter and
under a native build and compare magnitudes: a divergence shows up immediately as
~1e13 vs ~1.7e18. A regression spec should assert the two engines agree to within
a small tolerance, not merely that each is monotonic — a monotonicity-only oracle
passes on both epochs and is exactly why this survived.

## Re-verification (2026-08-09, parallel bug-list pass)

Confirmed PRIMARY over
`doc/08_tracking/bug/rt_time_now_nanos_has_two_different_epochs_2026-08-09.md`
(that doc is DUPLICATE-of-this-one — same root cause, filed the same day,
narrower implementation inventory, no ownership-note context). Re-read the
in-tree blocking note at `runtime_native.c:9124` (still present, unchanged)
and confirmed via grep that `rt_time_now_nanos`/`rt_time_now_micros` are
still baselined in
`scripts/check/runtime_symbol_lane_divergence_baseline.txt` — the explicit
"owned by another lane, do not fix as a side effect" condition still holds.
**Deliberately left unfixed**, consistent with the doc's own "Why this is
filed, not fixed" section: the correct fix is a semantic name-split
(`rt_time_monotonic_nanos` / `rt_time_unix_nanos`) across four
implementation sites including forbidden `src/compiler_rust/**`, not a
same-epoch patch to one side, and is owned by the lane-divergence baseline's
maintainer. No code changed in this pass.
