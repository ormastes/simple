# Bug: JIT wraps large i64 boundary constants (p60/p62/i64::MAX) to negative/zero

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

**Found**: 2026-08-09, via `scripts/check/check-engine-differential.shs`
(newly wired into pre-push this session, `DIFF_LANES=interpret,jit` fast
config) as a NEW unbaselined divergence: `i64_boundary_values`.

## Symptom

The interpreter and JIT engines disagree on large `i64` boundary constants
(`p60`, `p62`, `i64::MAX`-class values): the JIT wraps them to negative
values or zero, while the interpreter reports the correct value.

## Impact

Any code relying on large `i64` boundary constants under the JIT engine
(the default execution engine for `bin/simple run`) gets silently wrong
values. This is a correctness defect, not a performance issue.

## Root cause (found 2026-08-09, not yet fixed)

NOT a literal-lowering bug — the lexer, HIR→MIR lowering, and Cranelift
`iconst` emission all pass the full `i64` value through faithfully. The
actual defect is in the dynamic-value **tagged-pointer boxing scheme**:
`emit_box_int`/`emit_unbox_int` in
`src/compiler_rust/compiler/src/codegen/cranelift_emitter.rs:682-770`
(mirrored in the reference interpreter,
`src/compiler_rust/compiler/src/codegen/mir_interpreter.rs:757-770`):

```rust
// emit_box_int:   value << 3 | TAG_INT(0)
// emit_unbox_int: value >> 3   (arithmetic shift)
```

3 low bits are reserved for the type tag, leaving only 61 usable bits.
Boxing an `i64` with magnitude ≳2^60 shifts its top 3 bits out of the
64-bit word; unboxing then arithmetic-shifts garbage back in as sign bits.
Hand-verified the bit math reproduces every observed wrong value exactly
(e.g. `i64::MAX` = `0x7FFF...FFFF`, `<<3` drops the top 3 ones and shifts
in zeros → `0xFFFF...FFF8`, `>>3` sign-extends → `0xFFFF...FFFF` = `-1`,
matching the JIT's actual output bit-for-bit).

This is a **known bug family, not fresh**: the emitter code itself already
carries `DEFECT A`/`DEFECT B`/`Task #123` comments about this exact
`<<3`/`>>3` scheme corrupting heap handles, and the fixture's own header
names it ("tagged-pointer representation steals low bits (the `<< 3`
family)"). Same family as `reference_list_get_returns_value_shifted_left_3.md`
in `.claude` memory, wider blast radius than previously scoped.

**Why not fixed here**: the `<<3`/`>>3` tag scheme is the JIT's core
`Any`/dynamic-value representation, used pervasively for boxed list
elements, generic/Any-typed call arguments, closures, and pattern matching
— not a narrow, isolated site. A correct fix needs either (a) widening the
representation so large integers spill to a heap box instead of being
inline-tagged (adds a fast/slow-path decision at every box site), or (b)
reworking the tag layout — both cross-cutting changes to the calling
convention and GC value layout with real regression risk. Deliberately not
attempted blind.

**Suggested next step**: scope a fix to `emit_box_int`/`emit_unbox_int`
that detects overflow (`value != (value << 3) >> 3`, i.e. doesn't fit in
61 signed bits) and falls back to a heap-boxed `TAG_HEAP` allocation for
out-of-range integers, mirroring the DEFECT-A/B heap-passthrough pattern
already present in `emit_box_int`.

Until fixed, `check-engine-differential.shs` is wired in RED on purpose in
`scripts/check/pre-push-conflict-tree-guard.shs` (same convention as
`lint_binary_staleness_guard`/`native_object_cache_granularity_guard`) so
this stays visible rather than being silently baselined away.


## 2026-08-17 CORE-P1 triage: DID NOT REPRODUCE / fix present in current source

Verified against CURRENT SOURCE (content, not SHA ancestry) during the crit_01
CORE-P1 sweep. Fix present in current source. `src/compiler_rust/compiler/src/codegen/cranelift_emitter.rs:730-739` `emit_box_int` no longer emits an inline `val << 3` (which overflows 64 bits for any value >= 2^61); it calls `rt_value_int`, under a comment naming "int61 truncation (DEFECT A, 2026-08-09)". The runtime half is implemented at `src/compiler_rust/runtime/src/value/core.rs:272`: `if Self::fits_inline_int(i) { Self((i as u64) << 3) } else { <heap box> }` -- bit-identical for what fits inline, heap-boxed for what does not. ROOT CAUSE COLLAPSE: this single unguarded 61-bit box is also the root of interp_me_method_first_param_times8_conditional_2026-06-29 (its "x8" IS this shift).
