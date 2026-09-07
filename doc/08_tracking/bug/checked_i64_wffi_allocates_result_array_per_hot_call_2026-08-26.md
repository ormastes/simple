# Checked i64 WFFI allocates a result array per hot call

- **Status:** FIXED (2026-09-06) — see "Resolution" and the residual lane note
- **Filed:** 2026-08-26
- **Area:** cached dynamic SFFI call transport
- **Severity:** high — allocation and release occur on every checked call

## Evidence

`spl_wffi_call_i64_checked` represents `[status, value]` as a newly allocated
two-element runtime array in both the native C and Rust providers. The C harness
must explicitly release every result. `DynI64FnSlot.call_checked` uses this API
on the cached hot path, so symbol lookup is avoided but allocation remains.

The new typed boolean thunks do not share this defect: they use scalar status
plus caller-owned output and allocate nothing.

## Unblock condition

Add a cross-lane scalar `spl_wffi_try_call_i64_out` contract accepting the
existing argument array and `*mut i64` output. Initialize output to zero, return
typed bridge status, migrate `DynI64FnSlot.call_checked`, retain the public
`Result<i64, text>`, and benchmark the same cached no-op/zero provider before
and after with allocations, latency distribution, and peak RSS.

## History — the providers landed, the consumer was reverted

`ec6a500b422` ("perf(sffi): remove checked i64 result allocation", 2026-08-26)
already implemented the whole contract: the C provider
(`src/runtime/runtime_native.c`, `src/runtime/runtime.h`), the Rust native
provider (`src/compiler_rust/runtime/src/value/wsffi_native.rs`), the Rust
interpreter provider
(`src/compiler_rust/compiler/src/interpreter_extern/wsffi.rs`), the codegen
signature (`codegen/runtime_sffi.rs`), the JIT symbol table (`elf_utils.rs`),
`common/src/runtime_symbols.rs`, and both Simple consumers.

`9eb38c592b1` ("Session fixes + phase-2 SEGV diagnosis") then **reverted the
`src/lib/nogc_sync_mut/sffi/dynamic.spl` half** back to the allocating array
transport — the stale-whole-working-copy clobber pattern `.claude/rules/vcs.md`
§ "Sync must never clobber" describes. That same commit legitimately added the
`file_exists` pre-check and the `_sffi_dlopen_checked` / `_sffi_dlsym_checked`
writeback-loss fallbacks, so it could not simply be reverted.
`src/compiler_rust/lib/std/src/plugin/__init__.spl` was NOT clobbered and still
carries its migration.

## Measurement (2026-09-06, aarch64 Linux)

Allocation census by `--wrap`ping `malloc`/`calloc`/`realloc` around 10,000
checked calls into a no-op two-argument provider, single translation unit over
`src/runtime/runtime_native.c`
(`test/harness/wffi_i64_alloc_count_c_harness.c`):

| transport | allocations / 10,000 calls | per call |
|---|---|---|
| `spl_wffi_call_i64_checked` (array) | 20,000 | **2.00** |
| `spl_wffi_try_call_i64_out` (scalar out) | 0 | **0.00** |

Two allocations per call: the `SplArray` header and its element buffer. The
non-zero array figure is the control — it proves the counter discriminates, so
the scalar transport's zero is not a "nothing was counted" artifact.

Latency distribution and peak RSS were **not** measured; only the allocation
count was, which is what the fix is about. Recorded here rather than implied.

## Resolution

- `src/lib/nogc_sync_mut/sffi/dynamic.spl` — re-declared the
  `spl_wffi_try_call_i64_out` extern and added `_sffi_call_i64_checked`, the one
  canonical checked-integer helper. Both `DynI64FnSlot.call_checked` (the cached
  hot path) and `DynLib.call_checked` now delegate to it. The public
  `Result<i64, text>` contract, the `spl_wffi_call_i64_checked` extern, and its
  export are all retained, so no existing caller changes.
- `src/compiler_rust/runtime/src/value/wsffi_native.rs` — added three unit tests
  pinning the scalar transport's status table, its null-output rejection, and
  that a valid foreign zero stays distinguishable from a bridge failure.
- `test/harness/wffi_i64_alloc_count_c_harness.c` +
  `scripts/check/check-wffi-try-call-i64-out-zero-alloc.shs` — the allocation
  census and the cross-lane status table, in one runnable check.

### Cross-lane agreement

Both providers are pinned to the same status table, asserted by the C harness
and by the Rust tests with identical cases:

| case | status | output |
|---|---|---|
| valid call | 0 | foreign result |
| null function pointer | 2 | 0 |
| `nargs` beyond the argument array | 1 | 0 |
| `nargs` above 8 | 3 | 0 |
| null output slot | 1 | (untouched) |

`WFFI_OK/INVALID_ARGUMENT/NULL_FUNCTION/UNSUPPORTED_SIGNATURE` in the Rust
provider are `0/1/2/3`, byte-identical to `SPL_WFFI_*` in `runtime_native.c`.

### Residual: the seed interpreter lane does not carry `*mut` writeback

Measured 2026-09-06 on `bin/release/aarch64-unknown-linux-gnu/simple`:
`spl_dlsym_checked(handle, "abs", &mut sym)` returns status 1 with `sym`
untouched, and `spl_wffi_try_call_i64_out(fptr, [-7], 1, &mut out)` likewise
returns 1 — the same `BorrowMut` writeback loss `_sffi_dlopen_checked` already
works around. Migrating unconditionally would have turned every interpreter-lane
checked call into a bridge rejection.

`_sffi_call_i64_checked` therefore probes the lane once per failing call with
`spl_wffi_try_call_i64_out(0, [], 0, &mut probe)`: a provider that honours the
contract zeroes the slot and answers `NULL_FUNCTION` (2) without entering
foreign code, while a lane that cannot carry the out parameter rejects the shape
first and answers `INVALID_ARGUMENT` (1). On a probe of 1 the call falls back to
the allocating array transport. Consequences, stated plainly:

- **Compiled / native lane:** one bridge crossing, zero allocations, no probe —
  status 0 returns immediately. This is the hot path the record is about.
- **Seed interpreter lane:** still allocates, and now costs three crossings per
  call instead of one. Verified end to end against `libc` `abs`:
  `DynLib.call_checked("abs", [-7])` -> `Ok(7)`,
  `DynI64FnSlot.call_checked([-9])` -> `Ok(9)`, and a missing symbol still
  yields `E-SFFI-001: unresolved foreign symbol: ...`.
- Closing that residual means fixing `Value::BorrowMut` writeback in the seed
  interpreter, which is owned elsewhere; the probe removes itself the day that
  lane answers 2.

## Runnable check

```bash
sh scripts/check/check-wffi-try-call-i64-out-zero-alloc.shs
```

`PASS — 7 case(s) checked, array_transport_allocs=20000 per_call=2.0000,
out_transport_allocs=0 per_call=0.0000` (exit 0). `FAIL` exit 1; `ERROR —
nothing was checked` exit 2 when there is no C compiler, the harness is missing,
it builds nothing, or it reports zero cases.

Also run green with this change: `check-c-runtime-compiles-push.shs`
(`PASS — 126 file(s) compiled, 0 errors (5 skipped for unavailable external
dependencies)`), `check-wffi-i64-checked-c.shs` (exit 0),
`check-wffi-checked-admission.shs` (exit 0), `cargo check --release --bin simple`
(exit 0), and the three new `try_call_i64_out_*` runtime tests.
`check-dynlib-no-fabricated-zero.shs` FAILs identically before and after this
change (`invalid handles and missing symbols are not fail-closed`) — a
pre-existing red at `ef8b58f3dab`, untouched here.
