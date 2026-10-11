# Stage-2 Windows-MSVC link fails: 3 undefined `rt_*` externs from `sffi/diag.spl`

Date: 2026-10-11. Lane: Windows-MSVC bootstrap, stage 2 (Rust seed compiling the
pure-Simple compiler). Status: fixed in the runtime (this change); guard pending.

## Symptom

Release tip `4182b2d01b5`: 1225 modules compiled, 0 failed, then

    lld-link: error: undefined symbol: rt_debug_exit_success
    >>> referenced by libspl_objects.a(mod_1133.o):(…sffi__diag__debug_exit_success)
    lld-link: error: undefined symbol: rt_perf_dump_sdn
    lld-link: error: undefined symbol: rt_print_err
    VERDICT — ABORTED: stage=stage2 exit=1

The three lines sit below 785 `/FORCE:MULTIPLE` duplicate-symbol warnings, and
the one-line build error quotes the first warning, not the cause.

## Root cause

Introducing commit: **`e63e9dd5f6b`** (2026-10-10, "fix(caret): route leaf
providers through SoSix and share manager snapshot rules"). It added

    export use std.nogc_sync_mut.sffi.diag.{print_raw as sosix_print_raw}

to `src/lib/nogc_async_mut/sosix/host_facade.spl`. `host_facade` was already in
the compiler closure; the import pulled `src/lib/nogc_sync_mut/sffi/diag.spl`
in. Evidence from kept object sets: the 2026-10-09 build has `host_facade` and
no `sffi__diag__*` symbol; builds from `f429fd4967b` on have 13 and fail with
exactly these three names.

`diag.spl` wraps 13 runtime externs. Three had no native definition in either
runtime lane (`src/runtime/**`, `src/compiler_rust/runtime/**`):

| extern | previous backing |
|---|---|
| `rt_print_err(msg: text)` | none (already `GENUINELY_MISSING` in the 2026-08 censuses) |
| `rt_debug_exit_success()` | baremetal example stub only |
| `rt_perf_dump_sdn() -> text` | seed interpreter only (`interpreter_extern/time.rs`) |

Nothing calls the three wrappers: `llvm-nm -u` over the build's
`libspl_objects.a` lists `mod_1133.o` (diag itself) as the only referencing
object.

### Why only Windows

`libspl_objects.a` is linked `/WHOLEARCHIVE` and lld-link resolves symbols
before `/OPT:REF`, so an extern declared by any module in the closure must be
defined even when the wrapper is dead. The seed has a trap-stub retry for this
(`linker.rs`, "Windows undefined-symbol stub parity"), but the bootstrap sets
`SIMPLE_NO_STUB_FALLBACK=1`, which disables it — correctly, fail-closed. ELF
(`--gc-sections`) and Mach-O (`-dead_strip`) discard the dead section before
reporting undefined symbols. That is read from `linker.rs`, not measured on
those hosts.

## Fix

Definitions in both lanes, same semantics:

- `rt_print_err` — message to stderr, no trailing newline (delegates to
  `rt_eprint_value`).
- `rt_debug_exit_success` — hosted: flush stdout/stderr, `exit(0)`.
- `rt_perf_dump_sdn` — `"perf_regions:\n  []\n"`: no native lane has a
  perf-region recorder, so the table is empty; byte-identical to the
  interpreter's empty output.

C: `src/runtime/runtime_native.c`, `runtime.h`. Rust:
`src/compiler_rust/runtime/src/value/sffi/io_print.rs`, re-exported from
`value/mod.rs`. The interpreter table gains `rt_print_err` and
`rt_debug_exit_success` (it already had `rt_perf_dump_sdn`).
`scripts/check/unbacked_extern_baseline.txt` drops `rt_print_err`.

Not updated: `config/api/api_registry.sdn` still records `rt_print_err` as
`none, unbacked`. The file is generated (`gen-api-registry.shs`) from built
runtime archives and must be regenerated, not hand-edited.

## Latent: same failure, different names

Three more externs are unbacked in the Windows core-C lane and unreferenced by
the stage-2 closure today. The day a module declaring one enters the closure,
the stage-2 link fails the same way:

- `rt_write_file`
- `f32_from_bits`
- `spl_bits_to_f64`

## Guard

`check-stage3-closure-extern-ratchet.shs` (branch
`work/rel-robust-small-items-2-20261011`, `0fb6ceaee86`) computes exactly the
right set — externs declared in the bootstrap closure and not defined by the
compiled core-C lane, by `nm`. As written it would NOT have blocked this: its
Windows baseline was generated after `e63e9dd5f6b` and lists all three names
(plus the three latent ones) next to ~40 system-library imports, so they pass
as "baselined". It fails only on names new relative to that baseline.

Proposed minimal change: runtime-owned names (`rt_*`, `spl_*`) are never
baselinable — unbacked in the closure is a FAIL regardless of the baseline, and
`--generate-baseline` refuses to write them. The baseline keeps only
system-library imports, which the compile-without-link method cannot resolve.
With this fix landed the three names become stale in that baseline and must be
removed from it in the same change.

## Workaround used

Manual relink of the kept objects with a three-function C file:
`rel-p3run/workarounds/stage2-link-rt-symbols/` in the bootstrap storage
(outside the repo). Superseded by this fix.
