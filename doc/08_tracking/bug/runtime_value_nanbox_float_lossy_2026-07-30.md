# RuntimeValue NaN-boxing is lossy for all normal floats (2026-07-30)

## Symptom
`RuntimeValue.from_float(x)` → `as_float()` does NOT round-trip. For any normal
double (e.g. `3.5`) the result is a quiet NaN.

## Root cause (src/lib/nogc_sync_mut/runtime_value.spl, mirrored in all 4 tiers)
The tag lives in the **low 3 bits for every type, including float** (`TAG_FLOAT=0b010`).
A full 64-bit IEEE double cannot coexist inline with 3 low tag bits, so `from_float`
(:127, non-NaN branch) crams the double into the quiet-NaN payload:

    tagged = NAN_QUIET_BASE | (float_bits & 0x7FFFFFFFFFFFF) | TAG_FLOAT

This keeps only the low **51 mantissa bits** and discards sign + 11 exponent bits +
top mantissa bit. `as_float` (:260) just does `bits & ~TAG_MASK` then `bits_to_float`
— it never reconstructs the discarded bits, so the read-back is a NaN.

## Scope / severity
- Real, latent, silent. Affects the 3 non-self `from_float` call sites:
  `src/lib/nogc_sync_mut/src/table.spl`, `src/compiler/35.semantics/semantics/cast_rules.spl`,
  `src/lib/common/search/types.spl`.
- **NOT** the `print(3.5)` fullcli breaker: the backend interpreter formats
  `Value.Float(f64)` directly (`70.backend/backend/interpreter_calls.spl:516`,
  `"{f}"`), bypassing RuntimeValue. That breaker is the separate emergent
  ANY-erasure miscompile (see project_pure_simple_divergence_fix_2026-07-29).

## Fix options (architectural — NOT a one-liner, deferred by design)
The low-3-bit-tag scheme is incompatible with lossless inline doubles. Correct fixes:
1. **Offset NaN-boxing** — store real doubles by adding a constant so no double lands
   in the NaN-tag region; encode int/ptr/bool/nil inside the NaN space instead.
   Requires flipping the tag convention (doubles become the untagged default).
2. **Heap-box floats** — `from_float` allocates an f64 cell and stores a TAG_PTR to it.
   Simplest to reason about; costs an allocation per float.

Either changes `is_float`/`as_float`/`tag` semantics broadly and needs the tag
scheme's test suite. Do not hack in place.

## Discovery
Parallel divergence scan lane 4 (2026-07-30). Anchor-family sibling: the landed
`04a68b28` (logical-vs-bitwise operators) and `e9bee8a2baf` (gc_async_mut byte
serialization) fixes.
