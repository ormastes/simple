# todo_db row 574 (area runtime, P1) — premise is partly stale

Row 574 asks to "provide overflow-safe cross-platform monotonic millisecond
conversion and split QEMU runner elapsed timing from wall-clock artifact
stamps", and its note lists four concrete sub-claims. Two of them no longer
hold in the tree as of 2026-08-18. Recorded here rather than silently fixed,
per the rule that a stale citation is not proof and an invented fix is worse
than none.

## Sub-claim 1 — "platform_win.h ... QPC multiply-before-divide overflow" — STALE

`src/runtime/platform/platform_win.h:570-593` (`rt_time_now_nanos`,
`rt_time_now_micros`) already divides first:

    int64_t seconds   = count.QuadPart / freq.QuadPart;
    int64_t remainder = count.QuadPart % freq.QuadPart;
    if (seconds > INT64_MAX / 1000000000LL) return INT64_MAX;
    return seconds * 1000000000LL + (remainder * 1000000000LL) / freq.QuadPart;

There is no multiply-before-divide left, and the saturating guard is present.
`src/runtime/runtime_time.c:22-33` (`win_qpc_delta_to_nanos`) has the same
shape, and additionally measures a DELTA from a process-start baseline, which
keeps the operand small.

## Sub-claim 2 — "native_all rt_time_now_monotonic_ms using SystemTime wall clock" — STALE

`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:2335` now uses
`std::time::Instant` against a `OnceLock` process-start baseline, and carries a
doc comment explaining that the previous `SystemTime`/`UNIX_EPOCH`
implementation was a wall clock. The C provider
(`src/runtime/runtime_time.c:60-88`) uses `CLOCK_MONOTONIC`, also baselined.

## Sub-claim 3 — "simple_core core_process.spl Linux-specific CLOCK_MONOTONIC id/layout" — STILL LIVE

`src/runtime/simple_core/core_process.spl:130-158` hardcodes the clock id:

    val result = clock_gettime(1, ts)   # "CLOCK_MONOTONIC = 1 on Linux"

with a `malloc(16)` / two-`i64` `struct timespec` layout. `CLOCK_MONOTONIC` is
1 only on Linux (FreeBSD 4, macOS 6), so this reads a different clock on the
canonical FreeBSD bootstrap host. Two further divergences from the C provider
in the same functions: there is **no process-start baseline**, so these return
raw time-since-boot while `runtime_time.c` documents and returns
"nanoseconds from a process-local epoch" — two providers of the same symbol
with different absolute epochs.

Not fixed here: the id/layout half cannot be REPRODUCED on this Linux host,
and this lane's rule is reproduce-before-fix. It needs the FreeBSD QEMU
bootstrap host (`sh scripts/check/check-freebsd-bootstrap-qemu.shs`).

## Sub-claim 4 — runner elapsed-vs-wall-clock split — NOT ASSESSED

Left untouched; no claim made either way.

## Recommended row edit

Narrow row 574 to sub-claims 3 and 4 and drop 1 and 2, so the row stops
pointing at code that already satisfies it.
