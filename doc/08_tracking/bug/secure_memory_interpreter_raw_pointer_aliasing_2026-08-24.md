# Secure-memory interpreter raw-pointer aliasing
## FIXED 2026-11-11 (p3-interp11 lane)

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** FIXED 2026-11-11 (p3-interp11 lane) — the `Array.fill_span` fix
(f680394dddf8, 2026-11-07) is verified on the fresh seed 46fe8f6b6def. See the
2026-11-11 addendum at the end.
**Date:** 2026-08-24

## Failure

The interpreter previously rejected `rt_memory_barrier` as an unknown extern.
After registering the native-equivalent acquire, release, and sequentially
consistent barriers, the credential zeroization specification reaches the
foreign volatile writes but the caller-visible packed byte array is unchanged.

Measured interpreter evidence for
`credential_zeroization_spec.spl --mode=interpreter`:

| State | Result | Elapsed | Peak RSS |
| --- | --- | ---: | ---: |
| Before barrier registration | 3/6 pass; two unknown-extern failures | 22.79 s | 175,232 KiB |
| Barrier registered | 3/6 pass; zeroization assertions fail | 21.01 s | 178,528 KiB |
| Direct packed `data_ptr` experiment | 3/6 pass; zeroization assertions still fail | 20.68 s | 177,808 KiB |

The remaining authentication failure is pre-existing and independent of the
two zeroization assertions.

## Root cause boundary

Interpreter packed arrays use `Value::ByteArray(Arc<Vec<u8>>)`. Exposing
`Vec::as_ptr()` and writing through it is not a sound mutable API: shared `Arc`
aliases exist and Rust has not granted mutable access to the allocation. A
method-only fast path avoids the old O(n) widening allocation, but does not
repair ownership or mutation propagation and therefore is not an acceptable
fix.

## Required fix

Add a compiler-owned mutable byte-array operation that:

1. identifies and updates the caller's actual place rather than a cloned value;
2. obtains exclusive storage through the interpreter's normal write-back path;
3. performs one O(n) volatile wipe with no per-element allocation;
4. returns a typed report/status while preserving boolean semantics;
5. keeps raw pointers inside the runtime boundary;
6. has differential interpreter/native coverage and allocation evidence.

Until that exists, interpreter secure zeroization is not verified and must not
be advertised as a safe foreign-pointer wrapper.


## 2026-11-07 — fix implemented (round 15, work/r15-interp-design-20261107)

Measured on the release tip seed before the fix: the existing
`credential_zeroization_spec` passed 7/7, but only because the callee's
`bytes` parameter is an `Arc` clone of the caller's value and the raw
`rt_volatile_write_u8` loop mutated that SHARED allocation. Two probes made
the unsoundness visible: a top-level `rt_array_data_ptr_text(a)` addressed a
temporary (writing 0 through it left `a[0]` at 96, not 0), and a callee's
private copy (`var local = bytes`) wiped through the raw pointer never
reached the caller while the report still said `verified()`.

Fix (compiler-owned, no raw pointer in Simple code):

- New builtin `Array.fill_span(dst_off: i64, count: i64, value) -> i64`,
  sibling of `write_span`: in-place VOLATILE fill, returns the count written,
  `0` for `count <= 0`, `fill_span out of range: ...` (exit 1) for an
  out-of-range span, never grows the receiver. Interpreter: kernels
  `array_fill_span` / `byte_array_fill_span` (`interpreter_method/collections.rs`)
  reached through the mutating-method channel (`PlaceMutation::FillSpan`,
  identifier fast paths, `evaluate_method_call_with_self_update` write-back),
  so the fill lands on the resolved place's exclusive storage
  (`Arc::make_mut`) and is published by the normal `mut`-parameter write-back.
  Native: `rt_array_fill_span` in `src/runtime/runtime_native.c` and
  `runtime/src/value/collections.rs` (volatile stores + full fence); seed
  codegen maps `fill_span` like `write_span` (raw-count tagging included);
  pure-Simple lowering `lower_unresolved_array_fill_span`
  (`50.mir/_MirLoweringExpr/method_calls_literals.spl`) + LLVM backend decls.
- `src/lib/common/crypto/secure_memory.spl` takes every buffer as a `mut`
  parameter and wipes with `fill_span`; `rt_array_data_ptr*` /
  `rt_volatile_*` / `rt_memory_barrier` externs removed from the owner.
- Repro: `test/01_unit/lib/crypto/secure_memory_aliasing_spec.spl`
  (RED on the pre-fix seed: `method fill_span not found`, 0/6).
- Prevention: `test/01_unit/lib/crypto/secure_memory_fill_span_prevention_spec.spl`
  (general shape across representations and places) and the engine-parity
  fixture `test/fixtures/engine_differential/fill_span_secure_wipe.spl`.


## 2026-11-11 — P3 interp11 triage verdict: FIXED (verified on fresh seed 46fe8f6b6def)

The 2026-11-07 `Array.fill_span` fix (commit `f680394dddf8`, "interp:
Array.fill_span compiler-owned volatile fill; secure_memory on mut params")
is present at HEAD and verified by execution on the fresh Windows seed
(build-commit `46fe8f6b6def`), 2026-11-11, both interpreter-mode unit specs
green with `--mode=interpreter --no-cache`:

- `test/01_unit/lib/crypto/secure_memory_aliasing_spec.spl`: **6/6 passed**
  (was RED pre-fix: "method fill_span not found", 0/6).
- `test/01_unit/lib/crypto/secure_memory_fill_span_prevention_spec.spl`:
  **7/7 passed**.

This satisfies the row's six-point required fix: the wipe is compiler-owned
(`Array.fill_span`), reaches the caller's place through the interpreter's
mutating-method write-back (`Arc::make_mut` exclusive storage), does one O(n)
volatile fill, returns a typed count while preserving boolean semantics,
keeps raw pointers inside the runtime boundary (`rt_array_fill_span` /
interpreter kernels), and carries differential interpreter/native coverage
plus the prevention spec. No residual.
