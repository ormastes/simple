# JIT container boxing truncates any i64 outside -2^60 ..= 2^60-1

> **RESOLVED 2026-08-18 — STALE DEPLOYED SEED, not a live source defect.**
>
> The original root-cause section below (kept verbatim for the record) named
> Cranelift container fast paths that box with a bare `ishl_imm(raw, 3)`. That
> analysis was performed against the DEPLOYED binary `bin/simple`
> (sha256 prefix `4129e2a7d62e17a6`, mtime 2026-08-18 07:53 UTC) and it is
> accurate *about that binary*. It is **not** accurate about the source tree at
> `origin/main` `ce396605fef`, where BOTH halves of the fix are already present:
>
> - `codegen/instr/mod.rs:1535` and `codegen/cranelift_emitter.rs:739` already
>   lower `MirInst::BoxInt` through `rt_value_int` (landed `ae55a746719`,
>   2026-08-11), and `UnboxInt` through `rt_value_unbox_int`.
> - `runtime/src/value/core.rs:275` `from_int` already consults
>   `fits_inline_int` and falls back to `from_wide_int` (restored in
>   `1983ecdbce9`, 2026-08-17, after being clobbered by `e14a2ffb4df`).
>
> The container literal path is NOT one of the bare-shift fast paths: MIR
> lowering emits `BoxInt` before `ArrayLit` (verified with `SIMPLE_DUMP_MIR`),
> so it goes through the correct helper. The deployed seed simply predates
> `1983ecdbce9`.
>
> **Verification.** A compiler built from `ce396605fef` with no source change
> reads every value correctly on both engines; the same specs run against the
> stale `bin/simple` still fail. That two-sided result is the proof — a green
> that could not distinguish the two binaries would be vacuous.
>
> | fixture reading | interpret | jit (own build) | jit (stale seed) |
> |---|---|---|---|
> | `b60` (2^60) | 1152921504606846976 | 1152921504606846976 | -1152921504606846976 |
> | `b62` (2^62) | 4611686018427387904 | 4611686018427387904 | 0 |
> | `bmax` (i64::MAX) | 9223372036854775807 | 9223372036854775807 | -1 |
> | `bneg60` (-2^60) | -1152921504606846976 | -1152921504606846976 | -1152921504606846976 |
>
> `scripts/check/check-engine-differential.shs` now reports
> `PASS — 11 fixture(s) compared across 3 lane(s), 0 new divergences (1 baselined, 11 lane error(s))`
> exit 0. The `i64_boundary_values` divergence is gone and was **never
> baselined**. (The 11 lane errors are the `native` lane failing closed with
> "native-build produced no artifact" — a separate, pre-existing gap, not this
> defect; it is counted as an error, never as agreement.)
>
> **ACTION REQUIRED: redeploy `bin/simple`.** Nothing in the compiler or runtime
> needs changing; the shared seed must be rebuilt from `ce396605fef` or later.
> Until it is, every lane running the old seed still gets silent wrong answers.
>
> **Still-true residue from the analysis below:** the bare-shift sites it names
> (`closures_structs.rs:2229`, `calls.rs:1720/1885/2147/2347`, `actors.rs:59`,
> `mir_interpreter.rs:766/776`, `llvm/backend_core.rs:727`, `stubs.rs:718`) do
> still exist and still lack a range check. They were NOT changed here because
> none of them is on the path this defect travels — all of them box a value
> already masked to a byte/u32, a dict key, or a slot offset, and changing them
> blind, unreproduced, would be an unverifiable edit. They are worth a separate
> audit with its own reproducer.

---

## Original analysis (2026-08-18, against the stale deployed seed)

**Filed:** 2026-08-18
**Severity:** HIGH — silent wrong answer, no crash, no diagnostic
**Status:** RESOLVED (stale deployed seed) — see banner above. Originally filed as: OPEN. Root-caused to specific codegen sites; the fix is multi-site
(not contained) and is deliberately NOT attempted here — see "Why this was not
fixed in the same change".
**Found by:** `scripts/check/check-engine-differential.shs`, which this defect
is currently holding RED tree-wide (it is a full-tree probe, not range-bound,
so it blocks every push by anyone).

**Binary under test:** `bin/simple` ->
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
sha256 prefix `4129e2a7d62e17a6`, 59546088 bytes, mtime 2026-08-18 07:53:39 UTC.

---

## The blocking verdict

    FAIL — 1 unbaselined divergence(s) among 11 fixture(s) compared

The one unbaselined divergence is the fixture `i64_boundary_values`. The other
divergence, `utf8_slice_boundary`, is baselined and does not fail the gate.
`lane errors: 0` — **no lane failed to answer**, so this is not a harness
artifact of an errored lane being scored as a divergence.

Verbatim, from the two-lane run (`DIFF_LANES=interpret,jit`):

```
[i64_boundary_values] DIVERGENCE (NEW)
  interpret: small=42p60=1152921504606846976p62=4611686018427387904imax=9223372036854775807inegmax=-9223372036854775807boxed_p60=1152921504606846976boxed_p62=4611686018427387904boxed_imax=9223372036854775807arith=1shifted=1125899906842624
  jit: small=42p60=1152921504606846976p62=4611686018427387904imax=9223372036854775807inegmax=-9223372036854775807boxed_p60=-1152921504606846976boxed_p62=0boxed_imax=-1arith=1shifted=1125899906842624
```

(The harness strips all whitespace before comparing; that is why the readings
above are run together. See the header of
`scripts/check/check_engine_differential.spl` for why.)

Every `p*` scalar reading agrees. Only the `boxed_*` readings — the same values
read back out of a `[i64]` — differ.

## Real defect, not a harness artifact

Three independent reasons:

1. **No lane errored.** `lane errors: 0`. Both lanes ran to completion and
   printed a full transcript; the disagreement is between two real answers.
2. **The interpreter is self-consistent and the JIT is not.** In the same JIT
   transcript, `p62=4611686018427387904` and `boxed_p62=0` are the *same value*
   printed twice. A program cannot be right about a number as a scalar and
   right about it as a list element and report both — one of them is wrong, and
   round-trip identity says which.
3. **A positive control passes.** Small values agree on both engines through
   the identical code path (see the class table below).

## Measured: the exact boundary

Probe: `test/fixtures/engine_differential_probe/i64_container_boxing_sweep.spl`.
`s<n>` is the value through an identity fn; `b<n>` is the same value read back
out of a `[i64]`.

| reading | value stored | interpret | jit |
|---|---|---|---|
| `b00` | 0 | 0 | 0 |
| `b01` | 1 | 1 | 1 |
| `b32` | 2^32 | 4294967296 | 4294967296 |
| `b40` | 2^40 | 1099511627776 | 1099511627776 |
| `b58` | 2^58 | 288230376151711744 | 288230376151711744 |
| `b59` | 2^59 | 576460752303423488 | 576460752303423488 |
| **`b60`** | **2^60** | **1152921504606846976** | **-1152921504606846976** |
| **`b61`** | **2^61** | **2305843009213693952** | **0** |
| **`b62`** | **2^62** | **4611686018427387904** | **0** |
| **`bmax`** | **i64::MAX** | **9223372036854775807** | **-1** |
| `bneg60` | -2^60 | -1152921504606846976 | -1152921504606846976 |

Every corresponding `s<n>` scalar reading is correct on **both** engines,
including `smax`. The scalar half of this defect family
(`int61_bit_truncation_jit_scalars_and_native_container_boxing_2026-08-09.md`,
Defect A) is genuinely fixed in the deployed seed. **Defect B — the container
half — is not.**

The last row is the load-bearing one. `-2^60` survives while `+2^60` does not.
That asymmetry is not noise: it is the exact shape of a **61-bit signed
two's-complement field**, whose representable range is `-2^60 ..= 2^60 - 1`.
`+2^60` is the first value off the top of that band; `-2^60` is the last value
still inside it at the bottom.

## Defect class: which containers?

Probe: `test/fixtures/engine_differential_probe/i64_container_kinds.spl`,
value 2^62, with a small-value control through each identical path.

| container | interpret | jit | control (value 7), both engines |
|---|---|---|---|
| scalar | 4611686018427387904 | 4611686018427387904 | 7 / 7 |
| struct field | 4611686018427387904 | 4611686018427387904 | 7 / 7 |
| **`[i64]`** | 4611686018427387904 | **0** | 7 / 7 |
| **`[[i64]]`** | 4611686018427387904 | **0** | 7 / 7 |
| **tuple** | 4611686018427387904 | **0** | 7 / 7 |

Struct fields are correct; list elements, nested list elements and tuple
elements are not. The controls agree everywhere, which is what makes the
magnitude the variable under test rather than the container plumbing.

## Root cause

The runtime's value representation is already correct and already
two-representation:

- `src/compiler_rust/runtime/src/value/core.rs:304` —
  `pub const INLINE_INT_BITS: u32 = 61;`
- `src/compiler_rust/runtime/src/value/core.rs:324` — `fits_inline_int`, whose
  own doc states the range as `-2^60 ..= 2^60 - 1` and that "`-(1 << 60)` fits
  and `1 << 60` does not". This matches the measured boundary exactly.
- `RuntimeValue::from_int` consults `fits_inline_int` and falls back to
  `from_wide_int` -> a `TAG_HEAP` `HeapInt`; `as_int` decodes `as_heap_i64()`
  first. `rt_array_push` / `rt_array_get`
  (`runtime/src/value/collections.rs:1106` / `:681`) store and return the
  tagged word verbatim, so a wide element is legitimately a heap pointer in the
  slot and the runtime handles it.

**The Cranelift container fast paths never call any of that.** They box with a
bare shift and unbox with a bare arithmetic shift, so a wide value is truncated
on the way in and a `HeapInt` pointer is mis-decoded as a shifted integer on
the way out:

Boxing sites (bypass `rt_value_int`, no range check):
- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:2229` —
  `builder.ins().ishl_imm(raw, 3)`
- `src/compiler_rust/compiler/src/codegen/common_backend.rs:2606-2607` —
  array-literal global init, `ishl` by a `iconst(3)` then `rt_array_push`
- `src/compiler_rust/compiler/src/codegen/instr/actors.rs:59`
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs:1720, 1729, 1885, 2147, 2347`
- LLVM twin: `src/compiler_rust/compiler/src/codegen/llvm/backend_core.rs:727-731`
- C-stub twin: `src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs:718`
  — `rt_array_push(result, value << 3)`

Unboxing sites (`sshr_imm(raw, 3)` instead of `rt_value_unbox_int`):
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs:111, 484, 1705, 1775`
- MIR const-eval interpreter:
  `src/compiler_rust/compiler/src/codegen/mir_interpreter.rs:766` (`<< 3`) and
  `:776` (`>> 3`) — unconditional, no wide path.

The correct scalar path, for contrast:
`codegen/instr/mod.rs:1535` calls `rt_value_int`; `:1581` calls
`rt_value_unbox_int`. That is exactly the difference between the two halves.

## Suggested fix

1. Replace the container **boxing** shifts with
   `call_runtime_1(..., "rt_value_int", raw)` at `closures_structs.rs:2229` and
   `common_backend.rs:2606`, and `RuntimeValue::from_int(value)` at
   `stubs.rs:718`. Cost is one call instead of one shift, on container writes
   only.
2. Replace the container **unboxing** `sshr_imm(raw, 3)` at
   `calls.rs:111, 484, 1705, 1775` with `rt_value_unbox_int` — or keep the
   inline shift as a fast path and add a `tag == TAG_HEAP && heap_type == Int`
   fallback branch.
3. Mirror in `mir_interpreter.rs:766/776` and `llvm/backend_core.rs:727`.

**Caveat that must not be lost:** the `u64`/byte-packed array paths
(`is_u64_packed`, `maybe_packed_u64_load_word` / `..._store_word`)
intentionally store raw, unshifted 64-bit words. Those must stay raw. The fix
must touch only the generic tagged-element paths, which the existing
`u64_packed_condition` select already distinguishes.

## Why this was not fixed in the same change

The fix spans ~10 sites across three backends (Cranelift, LLVM, the C stub
emitter) plus the MIR const-eval interpreter, and every one of them needs a
rebuilt seed to verify — which means replacing the shared `bin/simple` that
several concurrent lanes are running against. That is out of scope for the
session that filed this. The two specs below are the durable artifact: they
fail today, they will pass the moment a fixed seed is deployed, and unlike
every example-based spec in this repo they are structurally capable of
observing the defect at all.

## Do NOT baseline this

`baselines()` in `scripts/check/check_engine_differential.spl` exists for
divergences that have been *decided to be acceptable*, not for ones that are
merely known. This is a silent wrong answer with no diagnostic. Adding it to
`baselines()` would turn the gate green while the defect remains, which is the
precise failure mode the harness was built to prevent — the harness's own
header says so about this exact fixture. The gate stays red until the codegen
is fixed.

## Specs

- `test/01_unit/bugs/jit_container_i64_boxing_truncation_repro_spec.spl` —
  reproducing. Currently 4 of 5 examples FAIL (the 5th is the non-vacuity
  gate, which passes).
- `test/01_unit/bugs/jit_container_i64_boxing_defect_class_spec.spl` —
  defect-class with positive control. Currently 5 of 8 pass and exactly the 3
  broken container kinds fail. The 5 passes are the controls (small value
  through every container) plus scalar and struct field, which are correct
  today and are pinned against regression.

Both specs **shell out** and run one probe program under
`SIMPLE_EXECUTION_MODE=interpret` and `=jit`, comparing transcripts. They do
not rely on the spec runner's own engine, and could not: `bin/simple test`
pins the child engine to `interpret` and de-JITs any module without a
`fn main`, so an in-process assertion can never observe a JIT defect — it
would pass identically whether the bug is present or fixed.

## Fixtures

- `test/fixtures/engine_differential_probe/i64_container_boxing_sweep.spl`
- `test/fixtures/engine_differential_probe/i64_container_kinds.spl`

## Related

- `doc/08_tracking/bug/int61_bit_truncation_jit_scalars_and_native_container_boxing_2026-08-09.md`
  — the original two-defect filing. Defect A (JIT scalars) is now confirmed
  fixed in the deployed seed; this document is the still-live Defect B, with
  the boundary and the container class measured precisely.
- `doc/08_tracking/bug/runtime_from_int_still_truncates_61bit_2026-08-17.md`
- `doc/08_tracking/bug/seed_jit_boxed_int_61bit_drops_high_bits_2026-07-22.md`
- `doc/08_tracking/bug/cross_engine_differential_29_disagreements_2026-08-17.md`
