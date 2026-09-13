# rt_hash_text disagreed across lanes, blocking bootstrap for two days — FIXED 2026-09-07

**Filed:** 2026-09-07
**Status:** FIXED — all four lanes verified to agree; see Verification below.
**Severity:** HIGH — blocked the Stage-2 sanity gate (`driver_native_capsule_result_valid_v1`
reported `receipt content mismatch expected-len=1141 actual-len=1128`).

## Summary

`rt_hash_text` had two DIFFERENT backing algorithms:

| lane | file (pre-fix) | algorithm |
|---|---|---|
| C runtime | `src/runtime/runtime_native.c:8704` | FNV-1a (offset `14695981039346656037`, prime `1099511628211`) |
| Rust interpreter extern | `src/compiler_rust/compiler/src/interpreter_extern/conversion.rs:77` | DJB2 (seed `5381`, `*33 + byte`) |
| Rust native runtime crate | `src/compiler_rust/runtime/src/value/collections.rs:4592` | DJB2 (same as interpreter extern) |
| Cranelift JIT inline fast path | `src/compiler_rust/compiler/src/codegen/instr/calls.rs` `compile_inline_hash_text` | DJB2 attempted, but its hand-rolled string-heap precondition checks (tag/kind-marker match) never held for real strings, so it silently fell back to a **content-independent 0** for every input |
| Pure-Simple twin | `src/runtime/simple_core/core_string.spl:740` | DJB2, mirroring the buggy inline fast path exactly (same 0-fallback design) |

`FileFingerprint.from_file` (`src/compiler/80.driver/driver_build/incremental.spl:49`)
builds `content_hash` from this extern. The capsule receipt is WRITTEN by the
interpreted `native_build_worker` (which resolved to the JIT lane's inline fast
path, always 0) and VERIFIED by compiled code (which linked the C or Rust
native runtime, a real deterministic non-zero value) — two hash strings of
different digit-width, hence the length mismatch.

## Why the "interpreted lane returns 0" symptom happened

The interpreter's `EXTERN_DISPATCH` table (`interpreter_extern/mod.rs:1588`)
correctly registers `conversion::rt_hash_text`, and that function was never
broken in isolation (DJB2 of `""` is `5381`, not `0`). The 0 came from a
DIFFERENT place: `bin/simple run` executes compiled/JIT code by default, not
the tree-walking interpreter, and the JIT's `compile_inline_hash_text`
intercepted the call before it ever reached a real runtime symbol. That
function reimplemented the string heap layout by hand in Cranelift IR
(`tag == 1`, `kind == 'STRI'` marker, length at `+8`, data at `+16`) and
branched to a literal `0` on any precondition mismatch. Those preconditions
never held for how strings are represented today, so it always fell through
to 0 — a fail-open sentinel indistinguishable from a legitimate hash.

This is a variant of the same defect a prior bug doc
(`rt_hash_text_returns_zero_under_jit_cache_freshness_vacuous_2026-08-17.md`)
diagnosed and claimed to have fixed by deleting the inline path — but
`compile_inline_hash_text` and its call site were both still present in this
tree, so that fix never actually landed (or was reverted). That doc's status
line has been corrected to point here.

## Fix

Canonical algorithm: **FNV-1a 64-bit**, matching the C runtime. Chosen over
DJB2 because the C/native lane's values are what real, already-computed
capsule receipts and cache hashes were built against; making the interpreter
side canonical instead would have meant migrating the native/compiled side,
which is the side every persisted artifact already agrees with.

1. `src/compiler_rust/compiler/src/interpreter_extern/conversion.rs`
   `rt_hash_text` — DJB2 → FNV-1a.
2. `src/compiler_rust/runtime/src/value/collections.rs` `rt_hash_text` — DJB2
   → FNV-1a (its `rt_str_hash` alias automatically follows, since it calls
   `rt_hash_text`).
3. `src/compiler_rust/compiler/src/codegen/instr/calls.rs` — deleted
   `compile_inline_hash_text` and its call site entirely. `rt_hash_text` now
   falls through to the ordinary `ctx.runtime_funcs` call path, which links
   directly to the real runtime symbol (already a registered codegen root
   per `common_backend.rs` and `runtime_sffi.rs`). No inline reimplementation
   of the string heap layout remains for this symbol, removing both the
   algorithm-choice question and the 0-fallback bug at once.
4. `src/runtime/simple_core/core_string.spl` `rt_hash_text` — DJB2 → FNV-1a
   (kept the existing tag/pointer/kind guards, only the hash body changed).
5. `src/runtime/runtime_native.c` and the pure-Simple ABI bridge
   `src/lib/nogc_sync_mut/src/hash.spl` were already FNV-1a; unchanged.

Out of scope (deliberately, to avoid over-reaching): `rt_str_hash` in
`core_string.spl` is a separate, independently-implemented symbol that
happened to share the same DJB2 body; it was not asked about by name and
`.hash()` for text is unaffected by it, so it was left alone.
`examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c` computes
FNV-1a correctly but masks the result to non-negative
(`& 0x7FFFFFFFFFFFFFFFULL`), a minor variant from the other C lanes (which
return the full signed 64-bit value); noted here, not fixed, since it is
example/board bring-up code outside the bootstrap lanes this bug blocked.

## Verification

Four-value table, re-measured on a freshly built seed (`cargo build --release
--bin simple`), same four inputs, across every lane:

| input | interpret | jit | default | native (`--backend cranelift`, Rust runtime) |
|---|---|---|---|---|
| `""` | `-3750763034362895579` | `-3750763034362895579` | `-3750763034362895579` | `-3750763034362895579` |
| `"abc"` | `-1792535898324117685` | `-1792535898324117685` | `-1792535898324117685` | `-1792535898324117685` |
| `"hello world"` | `8618312879776256743` | `8618312879776256743` | `8618312879776256743` | `8618312879776256743` |
| `"fn main(): print 1"` | `-1847740476456475755` | `-1847740476456475755` | `-1847740476456475755` | `-1847740476456475755` |

All four lanes agree exactly.

- `sh scripts/check/check-c-runtime-compiles-push.shs` → `PASS — 131 file(s)
  compiled, 0 errors (5 skipped for unavailable external dependencies)`.
- `cd src/compiler_rust && cargo check --release --bin simple` → clean.
- `test/01_unit/lib/nogc_sync_mut/hash_text_crosslang_spec.spl` (pre-existing
  C-MIG-0020 spec comparing the pure-Simple FNV-1a bridge against the
  `extern fn rt_hash_text` oracle) → `Results: 8 total, 8 passed, 0 failed`.

## Runnable check

`scripts/check/check-rt-hash-text-cross-lane.shs` — builds one probe `.spl`
file and runs it under `SIMPLE_EXECUTION_MODE=interpret`, `=jit`, the
untouched default, and a genuine native build linking the Rust runtime;
compares stdout across all lanes. Verdict is the last line of stdout
(`PASS — <n> lane(s) checked, ... 0 divergent` / `FAIL — ...` /
`ERROR — nothing was checked`), matching the house convention.

Proven to fail on the pre-fix shape: temporarily reverting only
`conversion.rs`'s algorithm back to DJB2 and rebuilding reproduces the
disagreement —

```
sh scripts/check/check-rt-hash-text-cross-lane.shs --simple-bin <pre-fix binary>
  MISMATCH: lane 'jit' disagrees with lane 'interpret': ...
FAIL — 4 lane(s) checked, 3 divergent
```

— and passes again once the fix is restored and rebuilt:

```
sh scripts/check/check-rt-hash-text-cross-lane.shs --simple-bin <fixed binary>
PASS — 4 lane(s) checked, 4 input(s) each, 0 divergent
```
