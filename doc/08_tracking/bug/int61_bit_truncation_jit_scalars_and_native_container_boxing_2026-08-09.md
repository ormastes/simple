# Integers needing 61+ bits are corrupted: JIT everywhere, native inside containers

Status: RESOLVED 2026-08-24 — ALL THREE LANES. Defects A and B (the int61
truncation this file is named after) were fixed and MEASURED on interpret and
jit on 2026-08-21; the native lane was closed 2026-08-24 by two DIFFERENT
defects (C: f64 boxed through %rdi against a `double` ABI; D: unmasked LLVM
shift count) — see "Native lane closed (2026-08-24)" at the END of this file.
The differential corpus now reports 13/13 AGREE across interpret, jit and
native with zero baselined divergences. See also "Resolution (2026-08-21)" for
what was actually wrong on jit, which is NOT what the earlier "Fix (Defect A)"
section below claimed had landed.
Found 2026-08-09 by the multi-engine differential harness
(`scripts/check/check_engine_differential.spl`) on its first run.
Binary under test: `bin/release/x86_64-unknown-linux-gnu/simple`, sha256
prefix `166c622b30c2257c`.

## Summary

An integer at or above `2^60` is silently corrupted. There is no warning, no
error and no crash: the program runs to completion and prints a wrong number.
The interpreter is correct for every value.

The three-lane comparison splits this into **two distinct defects**, which is
the finding a two-lane (interpret vs JIT) comparison would have merged:

| | scalar local / arg | element stored in a list |
|---|---|---|
| interpret | correct | correct |
| **jit** | **CORRUPT** | **CORRUPT** |
| **native (LLVM AOT)** | correct | **CORRUPT** |

- **Defect A — JIT scalars.** JIT-only. A plain `val`/argument holding a large
  integer is already wrong before any container is involved.
- **Defect B — container boxing.** Shared by JIT **and** native, so it lives
  in the common boxed-value representation rather than in either codegen. This
  is the more important of the two: native gets scalars right and still
  corrupts the same values on the way into a list.

## Measured

Fixture: `test/fixtures/engine_differential/i64_boundary_values.spl`.
`p*` are scalars through an identity fn; `boxed_*` are the same values read
back out of a `[i64]`.

| | interpret | jit | native |
|---|---|---|---|
| `small=42` | 42 | 42 | 42 |
| `p60` (2^60) | 1152921504606846976 | **-1152921504606846976** | 1152921504606846976 |
| `p62` (2^62) | 4611686018427387904 | **0** | 4611686018427387904 |
| `imax` (i64::MAX) | 9223372036854775807 | **-1** | 9223372036854775807 |
| `inegmax` | -9223372036854775807 | **1** | -9223372036854775807 |
| `boxed_p60` | 1152921504606846976 | **-1152921504606846976** | **-1152921504606846976** |
| `boxed_p62` | 4611686018427387904 | **0** | **0** |
| `boxed_imax` | 9223372036854775807 | **-1** | **-1** |

A separate narrowing probe established the cutoff exactly: `2^59`
(576460752303423488) is correct on the JIT, `2^60` is not. `2^40` is correct.

## Mechanism (inferred; consistent with every row)

The wrong values are exactly what a **61-bit tagged immediate** yields when
the surviving bits are sign-extended back to i64 — a 3-bit tag stolen from the
low end, with no range check on the value:

- `2^60` sets the sign bit of a 61-bit field, so it returns negative with the
  same magnitude.
- `i64::MAX` is all-ones across 61 bits, sign-extending to `-1`.
- `2^62` retains no bits inside the field, returning `0`.

Native agreeing with the interpreter on scalars but with the JIT on list
elements is what localizes Defect B to the shared boxing path: native only
boxes when a value enters a container, and that is precisely where it starts
losing bits.

This is the same `<< 3` tagged-pointer family as the documented `list.get`
shift defect, but here the value is destroyed on the way IN rather than
mis-read on the way out.

## Why no existing test catches it

`bin/simple test` pins every child spec to the interpreter, and a spec file
(top-level `describe`/`it`, no `fn main`) de-JITs regardless because
`describe`/`it`/`expect` are Rust interpreter intrinsics with no codegen
lowering. The spec corpus is structurally blind to both defects and will stay
green through them. See
`doc/08_tracking/bug/jit_test_suite_blind_spot_2026-07-30.md`.

Example-based tests also use small numbers, which round-trip fine — nothing
appears below 2^59.

## Blast radius

Any large integer constant on a compiled lane: hash seeds and primes
(FNV/xxHash offsets exceed 2^60), bitmasks, `i64::MAX` sentinels used as
"unset" or as a min-search initializer, and **nanosecond timestamps**
(current epoch-ns is ~1.7e18, well above the safe range).

Defect B is the dangerous one in practice because it needs no large literal in
the source — any large value computed at runtime is corrupted merely by being
stored in a list, on the **native** lane that ships. An `i64::MAX` sentinel
becoming `-1` inverts every `if x < best` comparison in a min-search.

## Reproduce

    bin/simple run scripts/check/check_engine_differential.spl
    # narrowed (native lane needs a full native-build, several minutes):
    DIFF_FILTER=i64 bin/simple run scripts/check/check_engine_differential.spl

## Root cause (read off the code 2026-08-09)

The inferred 61-bit field is confirmed exactly: it is the ABI contract's own
`v << 3` / `v >> 3` tag-box scheme
(`doc/04_architecture/compiler/array_value_abi_contract.md` §1.1), applied with
**no range check** anywhere in either tree.

**Defect B — container boxing (in `.spl`/C scope, FIXED).** Two mirrored sites
in the pure-Simple compiler, both of which the native lane uses:

- encode: `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`
  `box_runtime_value` — the integer arm emitted an unconditional
  `MirBinOp.Shl(v, 3)`.
- decode: same file, `decode_runtime_value` — the `is_integer` arm emitted an
  unconditional `MirBinOp.Shr(raw, 3)`.

So it is a **missing range check, not a wrong shift width**: `<<3`/`>>3` are the
specified widths, and the encoder simply had no fallback for a value that does
not fit the 61-bit payload. §1.1 already names the required behavior ("the
encoder traps or heap-boxes; silently truncating is a violation"), so the fix is
the contract's own escape hatch, not a new policy.

Fix, three trees:

- **T3 `src/runtime/runtime_native.c`**: new `RT_VALUE_HEAP_INT` ("INT1") leaf
  `RtCoreWideInt` — deliberately the same layout as `RtCoreFloat`, so it reuses
  every existing lifecycle/registry/transient-scope path — plus
  `rt_value_int_wide()` (in-range → the bit-identical `v << 3` immediate;
  out-of-range → registered heap box) and `rt_value_as_int_wide()` (heap-aware
  decode, bare `>> 3` otherwise). `rt_value_int`, `rt_value_as_int`,
  `rt_core_numeric_arg` and the print path are now heap-int aware.
- **T2 `expr_dispatch.spl`**: the `I64`/`U64` arms of `box_runtime_value` /
  `decode_runtime_value` now call those two runtime functions. Integer kinds
  **≤ 32 bits keep the inline shift** — their payload cannot overflow 61 bits, so
  they pay no call and their codegen is byte-for-byte unchanged.
- **T1 seed**: untouched (see Defect A).

Note the perf shape deliberately chosen: only 64-bit-wide integer boxes/unboxes
become an extern call; the in-range fast path inside that call is a compare plus
the same shift. If this shows up in a self-build profile, the follow-up is to
inline the range test in MIR (the builder has no `select`/branch helper today),
not to revert the check.

## Defect A — JIT scalars: RUST-SEED SCOPE, still OPEN

Not fixed here, deliberately: `identity(v)` corrupts the value with **no
container involved**, i.e. before any of the boxing sites above run, and the
native (LLVM AOT) lane — which shares T2's MIR — is *correct* on the same
scalars. That localizes it to the seed's Cranelift JIT lowering, which is
`src/compiler_rust/**` and therefore off-limits under CLAUDE.md's "fix .spl, not
Rust" rule. What a seed-lane effort must do:

- Find where a scalar `i64` local/argument acquires the tagged representation in
  the seed's Cranelift path — the `needs_int_unbox` decision in
  `src/compiler_rust/.../mir/lower/lowering_expr_struct.rs::lower_index_expr`
  and its `UnboxInt`/box counterparts (ABI contract §1.2 names these).
- Apply the same rule as T2/T3: a value outside `[-2^60, 2^60)` must be
  heap-boxed via `rt_value_int_wide` (the runtime entry point now exists and is
  linked by the seed too), never shifted.
- The seed must decode through `rt_value_as_int_wide` for symmetry, otherwise a
  wide value boxed by native code and read by JIT code shreds a pointer.

Until that lands, `jit` stays red for every `p*` and `boxed_*` row in the table
above, and the ABI contract's "seed Cranelift JIT VIOLATES" line stays true.

## Verification

- `src/runtime/test/rt_value_int_wide_selfcheck.c` (new) — 17 checks: in-range
  values keep the identical immediate (`1→8`, `-1→-8`, `42→336`), the four
  measured boundary values round-trip, `2^59` / `2^60-1` cutoff pair, the legacy
  `rt_value_int`/`rt_value_as_int` entry points agree, and a RAW untagged word
  still takes the bare shift. **SELFCHECK PASS**, and **sabotage-verified**:
  forcing `rt_core_int_fits_tagged()` to return 1 (the old always-truncate
  behavior) turns it red with 5 failures, so the oracle is fail-closed.
- Differential harness, unchanged fixture, before the fix: `interpret` correct
  on every row; `jit` corrupt on every row (`p60=-1152921504606846976`,
  `p62=0`, `imax=-1`, and the same for `boxed_*`) — reproduced directly, matching
  the table above.
- **Still owed**: the `native` lane re-measurement. The T2 half only takes effect
  once the self-hosted binary is rebuilt and redeployed (`bin/simple build
  bootstrap`), because `native-build` compiles the fixture with the *deployed*
  binary's compiled-in lowering, not from `src/compiler/**`. The fixture stays
  UNBASELINED — it was not touched, and the gate must stay red until both the
  redeploy confirms Defect B and the seed lane closes Defect A.

## Independent re-verification of Defect A (2026-08-09, separate session)

Re-ran the exact fixture via JIT (`bin/simple run
test/fixtures/engine_differential/i64_boundary_values.spl`, deployed
seed binary, no `SIMPLE_EXECUTION_MODE` override) and reproduced Defect A
identically, confirming it is still open exactly as this doc's "Defect A"
section describes:
```
small=42
p60=-1152921504606846976
p62=0
imax=-1
inegmax=1
boxed_p60=-1152921504606846976
boxed_p62=0
boxed_imax=-1
```
(The `boxed_*` rows above reflect the deployed binary's still-old T2 lowering,
pre-redeploy — consistent with "awaiting a bootstrap redeploy" in the status
line; not a regression, just the pre-redeploy baseline.) The native lane was
not re-measured this pass — it requires a `native-build`/bootstrap redeploy,
which this session's environment constraints exclude. No further action
taken; Defect A remains correctly characterized as Rust-seed-scope OPEN,
Defect B remains FIXED-in-source pending redeploy, exactly as already stated
above.

## Fix (Defect A) — 2026-08-09, Cranelift JIT + Rust seed runtime

The earlier note above guessed the site was in `src/compiler/70.backend/`. It is
not: **the JIT links the RUST runtime**
(`src/compiler_rust/runtime/src/value/`), not `src/runtime/*.c`, so Defect B's
C-side `rt_value_int_wide` could not be "reused" — the Rust twin did not exist.
The fix therefore has two halves.

### 1. Rust runtime — lossless wide-int box (twin of the C `rt_value_int_wide`)

- `value/heap.rs`: new `HeapObjectType::WideInt = 0x1D` + `HeapWideInt { header,
  value: i64 }` — same shape, registration and lifecycle as `HeapFloat`.
- `value/core.rs`: `RuntimeValue::from_int` range-checks (`int_fits_tagged`,
  `[-2^60, 2^60)`), keeping the **bit-identical `i << 3`** immediate in range and
  heap-boxing only what does not fit; `as_int` decodes a wide box. `is_int()` is
  deliberately UNCHANGED (172 call sites use it as a tag-shape/handle test).
- Value-identity follow-through, mirroring exactly what heap-boxed floats
  already needed: display (`io_print.rs`), `type_name`/`value_kind`, `Debug`,
  `rt_value_eq`/`rt_value_compare` compare wide ints **by value** not by
  pointer, and `free_transient_heap` frees the new leaf.
- `value/sffi/value_ops.rs`: new `rt_value_unbox_int` — a **total** tag-aware
  decode (wide box -> value; `TAG_INT` -> `>>3`; tagged true/false -> 1/0;
  anything else verbatim). Totality on any input, including a raw untagged i64,
  is what lets codegen replace an inline select chain with one call.
  C twin added in `src/runtime/runtime_native.c` + `runtime.h` for the
  Cranelift-AOT link.

### 2. Cranelift codegen — stop inlining the unchecked shift

Both live Cranelift paths (`codegen/instr/mod.rs` `compile_instruction`, and the
`CraneliftEmitter` in `codegen/cranelift_emitter.rs`) inlined `ishl 3` for
`BoxInt` and a `select` chain for `UnboxInt`, bypassing any runtime range check:

- `BoxInt` now calls `rt_value_int` (exactly mirroring how `BoxFloat` already
  called `rt_value_float`). The ANY/TypeId>=16 heap-handle passthrough guard and
  the i8/i16/i32/f32/f64 normalization are unchanged.
- `UnboxInt` now calls `rt_value_unbox_int`. This is required, not optional: a
  wide box carries `TAG_HEAP` and the old passthrough arm would have returned a
  raw pointer.
- `rt_value_unbox_int` registered in `codegen/runtime_sffi.rs` and as a codegen
  root in `common_backend.rs` (BoxInt/UnboxInt are synthesized by codegen, never
  as MIR call nodes, so a missing root = "unresolved external symbol" + silent
  whole-module drop to the interpreter).

Cost: one call per Box/UnboxInt where there was an inline shift. Correctness
first; if this shows up in a JIT profile the fast path can be re-inlined behind
a range-check branch with the call kept as the slow block.

### Evidence

`DIFF_FILTER=i64 DIFF_LANES=interpret,jit`, same fixture, same harness:

| | before (`166c622b30c2257c`) | after (`a4e1e5eb9bf4f88a`) |
|---|---|---|
| `i64_boundary_values` | **DIVERGENCE (NEW)** | **AGREE** |
| jit `p60` | -1152921504606846976 | 1152921504606846976 |
| jit `p62` | 0 | 4611686018427387904 |
| jit `imax` | -1 | 9223372036854775807 |
| jit `inegmax` | 1 | -9223372036854775807 |
| jit `boxed_*` | corrupt | all correct |

Full harness, both lanes, 11 fixtures: **10 AGREE, 0 NEW divergences** (the one
remaining divergence is the pre-existing baselined `utf8_slice_boundary`).

Unchanged-behaviour probe (below the cutoff and around it): `2^59`, `2^59 - 1`,
`-2^59`, `-42`, list elements, `bool` — identical on both lanes before and
after. (`opt = <value:0x7>` on the JIT is a SEPARATE pre-existing Option/`??`
defect, present identically on the old binary.)

Test coverage run: `cargo test --release -p simple-runtime` (1117 pass) and
`-p simple-compiler --lib -- codegen::` (934 pass). The failures in both suites
(8 and 5 respectively — dict/`is_nil`, VHDL `UnboxInt` unsupported,
`rt_dir_exists` duplicate spec, `mir_inline` "no entry found for key") were
**verified pre-existing at HEAD** by re-running them against the HEAD sources.

### Not done / follow-ups

- The **native (LLVM AOT)** lane's `UnboxInt` is in
  `codegen/llvm/functions.rs`, deliberately out of scope for this change (a
  concurrent lane owns that file). Defect B's native container fix already
  landed via the C runtime; the LLVM `BoxInt`/`UnboxInt` inline shift should get
  the same `rt_value_int`/`rt_value_unbox_int` treatment for full parity.
- The Cranelift fast path is a call, not an inlined range-check branch.

## Resolution (2026-08-21) — the producer was never wired; only the readers were

Re-measured at `origin/main` `f5823c5ab74` with a seed built from a clean
worktree (sha256 `53af156a5bbac8db`). The differential harness reported
`i64_boundary_values` **still DIVERGENT**, but not in the shape this file
describes: `p60`/`p62`/`imax`/`inegmax` (scalars) were CORRECT on the JIT and
only the `boxed_*` rows were wrong. That difference is the whole finding.

**The earlier "Fix (Defect A)" section above overstated what landed.** Its
codegen half is real and present: both Cranelift emitters call `rt_value_int` /
`rt_value_unbox_int` rather than inlining `ishl 3`, and both are registered as
codegen roots. Its RUNTIME half was not:

```rust
// runtime/src/value/core.rs, at origin/main
pub fn from_int(i: i64) -> Self {
    // Sign-extend to fit in 61 bits
    // The tag is 0, so we just shift
    Self((i as u64) << 3)          // <- no range check, ever
}
```

`HeapInt`, `HeapObjectType::Int`, `as_heap_i64`, the display arm, the equality
arm, the `value_kind`/`type_name` arms and the transient-free leaf entry all
existed — a complete READER half with **no producer**. `fits_inline_int` existed
too, and a doc comment on it said in as many words that `from_int` does not
consult it and that `runtime/tests/boxed_int_wide_roundtrip.rs` was expected to
be RED. It was: 3 of its 6 tests failed.

Scalars looked fixed only because MIR never boxes them — `print("{big}")` on a
local lowers to a direct `rt_raw_i64_to_string` with no `BoxInt` at all
(confirmed with `SIMPLE_DUMP_MIR`). So a scalar probe exercised none of the
fixed path, and reported green for the wrong reason. Anything entering a
container hit `BoxInt -> rt_value_int -> from_int` and was truncated.

### What changed

- `runtime/src/value/core.rs` — `from_int` consults `fits_inline_int`: in-range
  values keep the **bit-identical** `(i as u64) << 3` immediate, so every
  consumer that pattern-matches `TAG_INT` or untags by hand is unaffected; only
  what cannot fit allocates a `HeapInt`, mirroring `from_float`/`from_u64`
  exactly (same `track_transient_heap`, same OOM fallback to the lossy inline
  form rather than a crash). `as_int` decodes the box via `as_heap_i64` first —
  required, because a wide box carries `TAG_HEAP` and the inline sign-extension
  would otherwise return a raw POINTER. `is_int()` is deliberately UNCHANGED.
- `runtime/src/value/sffi/value_ops.rs` — `rt_value_unbox_int` handled the
  UNSIGNED box (`as_heap_u64`) but not the signed one, so a wide `HeapInt` fell
  through to its verbatim arm. Added the `as_heap_i64` arm.
- `compiler/src/codegen/llvm/functions.rs` — the LLVM lane's `BoxInt`/`UnboxInt`
  still inlined the unchecked `shl 3` / select chain. Given the same treatment
  as Cranelift, guarded to a 64-bit runtime int type so narrower targets keep
  the old inline form. This is the follow-up the previous section listed as "Not
  done"; it is **compile-verified only** — see "Still owed" below.

### A second, independent defect found while testing the neighbours

`INT64_MIN / -1` lowered to a bare `sdiv`. x86 `idiv` raises #DE for the one
signed quotient it cannot represent, so the JIT died with **SIGFPE (rc 136)**
while the interpreter wrapped to `INT64_MIN`. Wrapping is this language's
integer rule — `0 - INT64_MIN` and shifts `>= 64` (masked count) already agreed
on BOTH engines — so the JIT was the wrong engine, and a trap was never the
documented semantics. `compiler/src/codegen/instr/core.rs` now divides by 1 and
negates when the divisor is `-1`, and selects 0 for `%`. Division by ZERO is
deliberately untouched: it still traps, exactly as before.

### Evidence

| | interpret | jit (before) | jit (after) |
|---|---|---|---|
| `p60`, `p62`, `imax`, `inegmax` (scalars) | correct | correct | correct |
| `boxed_p60` | 1152921504606846976 | **-1152921504606846976** | 1152921504606846976 |
| `boxed_p62` | 4611686018427387904 | **0** | 4611686018427387904 |
| `boxed_imax` | 9223372036854775807 | **-1** | 9223372036854775807 |
| `imin / -1` | -9223372036854775808 | **SIGFPE, rc 136** | -9223372036854775808 |

Full corpus, `DIFF_LANES=interpret,jit`:
`PASS — 13 fixture(s) compared across 2 lane(s), 0 new divergences (0 baselined, 0 lane error(s))`.

Tests: `runtime/tests/boxed_int_wide_roundtrip.rs` 6/6 (was 3/6, RED by design —
3 new tests added there: `rt_value_unbox_int` decode, value-not-pointer
comparison, and an exact-boundary test asserting the in-range encoding is
byte-identical to the pre-fix one). New `compiler/tests/i64_boundary_jit.rs`,
3/3, executing real Cranelift: wide values through containers on both sides of
2^60, signed div/rem at `INT64_MIN / -1` plus ordinary-value controls, and
shift counts at and past the word width.

### Still owed

- **The native (LLVM AOT) lane was not measured.** It is a `LANE_ERROR` at this
  tip for an unrelated pre-existing reason: `native-build` fails with
  ``semantic: method `replace` not found on type `function` (function
  'hash_text' was not called)`` before any fixture runs. The LLVM
  `BoxInt`/`UnboxInt` change therefore has a `cargo check`/`build` behind it and
  nothing more. Do not read this record as evidence about native.
- `codegen/mir_interpreter.rs`'s `emit_box_int`/`emit_unbox_int` still do a bare
  `<< 3` / `>> 3`. That emitter models values as plain `i64` with no heap at
  all, so it is self-consistent (`box` then `unbox` is the identity) and no
  differential lane runs it — but it cannot represent a wide box and would need
  a different model to. Left alone deliberately.
- The Cranelift and LLVM fast paths are a CALL, not an inlined range-check
  branch with the call as the slow block.

## Native lane closed (2026-08-24) — and it was NOT int61 truncation

The "Still owed" item above ("the native (LLVM AOT) lane was not measured") is
now discharged. Measured at `origin/main` `dcc1e682940` from a clean worktree,
seed sha256 `a1387e23c4f015aa`; fixed by `5fc2a871e35`. Both remaining
unbaselined divergences —
`i64_boundary_values` and `f64_roundtrip` — are fixed, but **neither one was the
61-bit tag truncation this file is named after.** That half is genuinely fixed:
every `boxed_p60`/`boxed_p62`/`boxed_imax` row measured CORRECT on native before
either change below. Keep that distinction; folding these two into the int61
narrative would misdescribe both.

`native-build` loads `src/compiler/**` as SOURCE (the build log shows
`70.backend/backend/_MirToLlvm/core_codegen.spl` being read), so both fixes are
pure-Simple and take effect with no bootstrap redeploy.

### Defect C — f64 boxed through the wrong ABI register (`f64_roundtrip`)

`box_runtime_value`'s F64/F32 arms bitcast the double to i64 and passed **that**
to `rt_value_float`. The C runtime's parameter is a `double` — it has been since
`native_lane_prints_every_f64_as_denormal_garbage_2026-08-10`, whose comment in
`runtime_native.c` says in as many words "Keep this a `double`". The `.spl` side
still carried the stale claim that the ABI was `rt_value_float(int64_t
raw_bits)`, so under SysV x86-64 the caller put the payload in **%rdi** while the
callee read **%xmm0**. Every f64 entering a container boxed whatever was left in
%xmm0.

Measured, bit-level, before:

    movabs $0x3ff8000000000000,%rdi      # bits of 1.5 -> INTEGER register
    call   3570 <rt_value_float>         # reads %xmm0

after:

    movsd  -0x1e60(%rip),%xmm0
    call   3580 <rt_value_float>

| probe | interpret | native (before) | native (after) |
|---|---|---|---|
| `[1.5,2.25,3.125][0]` | 1.5 | 4.07677...e+90 (stale %xmm0) | 1.5 |
| `...[1]` | 2.25 | 0.0 | 2.25 |
| `...[2]` | 3.125 | 0.0 | 3.125 |
| `list_sum` | 6.875 | 4.1941340156960803e-76 | 6.875 |

The garbage was diagnostic: `4.194...e-76` has the bit pattern
`0x303030313d676962`, i.e. the ASCII bytes `big=1000` left over from the
preceding `print`.

Fix: `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` — pass the `f64`
operand itself (and declare the FuncPtr param as `f64`) in both the F64 and F32
arms. `bits` is retained only for the `??` fallback's legacy inline form.

### Defect D — unmasked LLVM shift count (`i64_boundary_values`)

LLVM's `shl`/`lshr`/`ashr` are **poison** when the shift count is >= the
operand's bit width. This language defines an over-wide shift as a MASKED count
(`count & (bits-1)`) — the fixture says so explicitly, x86/aarch64 mask in
hardware, and the interpreter and Cranelift JIT already agreed. Only the LLVM
lane disagreed, latching whatever register poison resolved to (a different
garbage value on every build).

| probe | interpret | native (before) | native (after) |
|---|---|---|---|
| `1 << 64` | 1 | 102404399226010 | 1 |
| `1 << 65` | 2 | 102404399225872 | 2 |
| `imax >> 64` | 9223372036854775807 | 102404399226017 | 9223372036854775807 |
| `one << c` (variable) | 1 | 102404399226206 | 1 |
| `1 << 63` (control) | -9223372036854775808 | same | same |
| `1 << 3` (control) | 8 | 8 | 8 |

Fix: new `masked_shift_amount` in
`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`, applied to the
`Shl`/`Shr` arms; twin `masked_shift_amount_ref` applied to the same defect in
`src/compiler/70.backend/backend/llvm_lib_translate_expr.spl` (defect-class
neighbour). Cost is nil in practice: a literal count constant-folds and a
variable count's `and` is dropped by the x86/arm backends, which mask anyway.
SIMD shifts route through `translate_simd_binop` and are untouched.

### Evidence

Full corpus, all three lanes, verbatim last two lines of
`sh scripts/check/check-engine-differential.shs` (exit 0):

```
PASS — 13 fixture(s) compared across 3 lane(s), 0 new divergences (0 baselined, 2 lane error(s))
PASS — 13 fixture(s) checked, unbaselined divergence(s)=0
```

`[f64_roundtrip] AGREE` and `[i64_boundary_values] AGREE`. Neither fixture was
baselined — both genuinely agree across interpret, jit and native.

The 2 lane errors are pre-existing and unrelated (`closure_runtime_facing`:
`unresolved method call: find`; `list_index_and_get`: `unresolved method call:
get`) — both are MIR-lowering gaps, and BOTH were verified to fail identically
at base `dcc1e682940` with these changes stashed (`list_index_and_get` ->
`unresolved method call: get`, `closure_runtime_facing` -> `unresolved method
call: find`, each rc=1).
