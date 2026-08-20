# Arrays sourced from a module-level `val` index 15x slower in the JIT — hoisting does not help

**Status:** OPEN (SIMPLE-CAPABILITY / PERF-REGRESSION root cause)
**Filed:** 2026-08-18
**Found by:** root-causing crc32_text_codegen_lane_14x_slower_than_c_2026-08-18.

## Measured (strict-JIT lane, fixed seed, 1M indexed reads of a 4-elem [i64])

```
val table = MODULE_TABLE (hoisted before loop) : 70,975 us  (~71 ns/read)
identical table built locally via push()       :  4,632 us  (~4.6 ns/read)
```

The hoisted local alias keeps the slow representation: indexing an array
whose identity originates from a module `val` takes a boxed/dispatch path on
every read. Additional finding from the same probes: `text.bytes()` costs
~28 ns/byte in the JIT (58 us for 2,090 bytes) — a second slow builtin path.

## Impact

Any hot loop reading a module-val lookup table (CRC/AES/S-box/base64 tables —
the standard shape for pure-Simple codecs) is deoptimized ~15x regardless of
call-site hygiene. This accounts for the bulk of crc32_text's 14.4x-vs-C gap
(1.045M table reads x ~66 ns delta ≈ 69 ms of the 83 ms).

## Fix

Compiler: give module-val arrays the same unboxed representation/access path
as locals (or const-promote immutable module vals). Library mitigation applied
meanwhile in gzip/crc.spl: per-call local copy of the table (256 pushes ≈ us,
recovers ~4.6 ns/read indexing in the JIT; negligible vs the per-byte loop in
the interpreter).

## Follow-up probes (same day): complete crc32 cost model in the JIT lane

- Indexing a `bytes()`-RETURNED array is fast (~4.1 ns/read) — the slow
  representation is specific to module-val-sourced arrays.
- `text.byte_at(i)` costs ~44 ns/call — worse than bulk bytes()+index; not a
  workaround.
- Post-mitigation per-call budget (2,090-byte body, measured 88 us total vs
  C 11.5 us): bytes() ≈ 58 us (66%, the builtin bulk-conversion bug),
  per-call table copy ≈ 26 us (mitigation cost, removable only by fixing the
  module-val representation), CRC loop itself ≈ 19 us (~9 ns/byte — near-C).
  ⇒ With both compiler fixes the pure-Simple loop is already at parity
  shape; no further library-level work is productive.

## bytes() bulk-fill FIX landed (same day): 26,393 -> 1,964 us per 500x2090B

`rt_string_bytes` (runtime/src/value/collections.rs) now bulk-fills the
exact-capacity array's element slots directly and publishes len once,
instead of one rt_array_push per byte. Measured with a verified fresh build
(first attempt was a cwd-broken cargo run masked by a pipe — the classic
exit-code trap; re-measured after a real rebuild):
- bytes(): ~28 ns/byte -> ~1.9 ns/byte (13x)
- crc32_text codegen lane: 44,128 -> 20,150 us => 3.5x vs C (from 14.4x).
Remaining gap: per-call table copy (~13 ms/500 calls, removable only by the
module-val representation fix) + near-C CRC loop.

## SEVERITY UPGRADE (same day): fn-initialized module-val arrays read WRONG VALUES via the fast path

Two distinct classes, measured on the current fixed seed (strict JIT):

| module-val initializer | typed hoisted read (`val t = V` then `t[i]` in hot loop) |
|---|---|
| array LITERAL (`val V = [1,2,3,4]`) | CORRECT but ~73-80 ns/read (annotation does not help) |
| function call (`val V = make()`)    | ~4 ns/read but returns WRONG VALUES |

Repro for the wrong-value class: switching gzip/crc.spl's loops from
`_table_copy()` back to direct `val table = _CRC32_TABLE` makes the
CRC-32 KAT ("123456789" -> 0xCBF43926) FAIL under SIMPLE_JIT_STRICT=1
while the same code passes interpreted. This matches module_pass.rs's own
comment trail: `global_init_values` stores only const-evaluable
initializers — a function-call initializer's result is never stored (the
"gap 8 write-side half" explicitly marked untouched), so the typed fast
path reads an uninitialized slot. Consequence: EARLIER "fast" module-val
probe numbers (4.1 us/1M) in this file are value-unverified and likely
measured zero-reads — treat only KAT-verified numbers as real.

The `_table_copy()` mitigation in gzip/crc.spl is therefore load-bearing
for CORRECTNESS, not just speed. Do not remove it until this bug is fixed
and the crosslang KAT passes under strict JIT with direct module-val reads.

## COMPILER FIX #2 (same day): fn-call initializer return-type inference — KAT now PASSES with direct reads

module_pass.rs: `val TABLE = make_table()` now inherits the callee's declared
return type instead of ANY (declaration-order bounded, same contract as the
dynamic-init ordering). Measured on the fixed build, strict JIT:
- direct module-val KAT: FAIL (tagged garbage) -> **KAT-OK**
- crc32-shaped loop with direct table reads: 12,988 us per 500x2KB
  => 2.25x vs C (from 19,544 us with the copy mitigation; 82,911 at session
  start — a 6.4x total improvement, 14.4x -> 2.25x).

## COMPILER FIX #3 (2026-08-20): unannotated array-literal module vals — the LAST slow/wrong literal shape

The remaining "array LITERAL is CORRECT but ~73-80 ns/read" row above was
mis-attributed: the split is not literal-vs-fn-call, it is **annotated vs
unannotated**. `val T: [i64] = [...]` was already fast and correct; `val T =
[...]` (no annotation) registered the global as ANY, which both forces the
boxed dispatch path AND makes `record_const_array_init` derive
`element_type = ANY`, so elements are consumed as raw i64 without unboxing.

Fix: `module_pass.rs` now infers a concrete `[i64]`/`[text]` type for an
unannotated module-level array literal whose elements are all const-evaluable,
in all three global-registration arms (`Node::Let`, `Node::Static`,
`Node::Const`). New helper `infer_const_array_type`. Heterogeneous/dynamic
literals keep the previous ANY behaviour.

A/B on two builds of the same tree differing only by this hunk
(`SIMPLE_JIT_STRICT=1`, 1M indexed reads, checksum must be 27500000):

| row | before | after |
|---|---|---|
| local_control | 4,903 us / OK | 4,637 us / OK |
| module_val_annotated | 4,901 us / OK | 4,965 us / OK |
| **module_val_unannotated** | **47,390 us / GARBAGE** | **4,387 us / OK** |
| module_val_typed_fn_init | 4,367 us / OK | 4,633 us / OK |

=> 10.8x faster and value-correct. Reproduce benchmark shipped at
`src/app/test/bench/bench_module_val_index.spl`. Regression: 8 targeted
global/array/const unit specs green on the fixed binary.

STILL OPEN (distinct shape, not fixed here): `val T = make()` where the callee
has **no declared return type** stays ANY and still returns garbage (measured
7,396 -> 7,074 us, checksum wrong on both). Fix #2 only inherits a *declared*
return type; inferring it from the callee's body is a separate change.

NOT DEPLOYED: this fix is in the working tree only. `bin/simple` still carries
the pre-fix seed, so `gzip/crc.spl`'s `_table_copy()` mitigation must stay.

DEPLOYMENT DEPENDENCY: gzip/crc.spl keeps `_table_copy()` until a compiler
carrying this fix is DEPLOYED — on the current deployed binary, direct
module-val reads still produce silently wrong values in the JIT lane. Also
requires the callee to declare its return type: `fn crc32_table():` (untyped)
must become `-> [i64]` when the switch happens. Prereqs also include the
all-dynamic-inits fix (previous section) for multi-module units.

## Exposure scan (2026-08-20, main session)

The garbage-value half of this defect is a CORRECTNESS landmine, not just a
perf gap, so the exposed population was counted rather than left implicit.
`/usr/bin/grep -rnE '^(pub )?val [A-Za-z_][A-Za-z0-9_]*[[:space:]]*=[[:space:]]*\[' src/ --include=*.spl`
returns **129 module-level unannotated `val` array literals** (anchored to
column 0 — the unanchored variant returns 1150, but that sweeps in function
locals, which are unaffected).

Notable among them, and the reason this is filed as more than a benchmark
result: `src/lib/common/bcrypt/types.spl:36,49,117,185,253` — the Blowfish
`P`/`S0`-`S3` init tables. On the currently DEPLOYED (pre-fix) binary those
read as undecoded raw i64 in the JIT lane, which would silently produce wrong
hashes rather than fail loudly. Other hits include
`js/engine/module_loader.spl:27` (`CORE_MODULES`) and
`notebook/gpu_mode_resolver.spl:69` (`GPU_AUTO_PROBE_ORDER`).

The compiler fix above covers these: all-const-evaluable `i64`/`text` literals
now infer `[i64]`/`[text]` instead of ANY. They remain exposed only until a
carrying compiler is deployed — see NOT DEPLOYED above. No source change was
made to the 129 sites; annotating them is a viable belt-and-braces mitigation
if a deploy stays blocked, but was not done here (129-site churn against a
fix that already addresses the class).
