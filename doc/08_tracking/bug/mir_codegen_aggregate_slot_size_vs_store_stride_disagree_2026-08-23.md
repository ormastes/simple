# codegen.spl sizes an aggregate stack slot with one model and writes it with another

- **Filed:** 2026-08-23
- **Status:** OPEN — found by static trace; NOT executed/observed, NOT repaired
- **Severity:** CRITICAL (stack slot overflow on the live pure-Simple JIT path)
- **Source:** `src/compiler/70.backend/codegen.spl` — `compile_inst`, `case Aggregate` (~L373) and `aggregate_type` (L585)
- **Found by:** MIR construct-matrix lane, while determining the blast radius of
  `mir_type_simd_vector_size_bytes_returns_8_2026-08-23.md`
- **Sibling record:** `mir_type_simd_vector_size_bytes_returns_8_2026-08-23.md`

## Summary

The aggregate-construction arm allocates a stack slot using `size_bytes()` (a
**packed sum** model) and then writes into it at a **hardcoded 8-byte stride**.
The two models disagree, and the allocation uses the smaller one.

```
val type_ = self.aggregate_type(kind)
val size  = type_.size_bytes()
val slot  = cranelift_stack_slot(self.current_ctx, size, 8)
var offset = 0
for operand in operands:
    ... cranelift_store(self.current_ctx, v, addr, 0)
    offset = offset + 8          # "Assume 8 bytes per element"
```

`aggregate_type` (L585) discards the real type first:

```
case Array(type_): type_                      # the ELEMENT type, not the array
case Tuple:        MirType(kind: MirTypeKind.I64)
case Struct(_):    MirType(kind: MirTypeKind.I64)
case Enum(_, _):   MirType(kind: MirTypeKind.I64)
```

## Consequence

| aggregate | slot size | writes reach | overflow |
|---|---|---|---|
| `Tuple`/`Struct`/`Enum`, N operands | **8** | `8*(N-1)` | **`8*(N-1)` bytes** |
| `Array` of `I32`, 4 elements | **4** (element size) | 24 | **28 bytes** |
| any 1-field aggregate | 8 | 0 | 0 (accidentally correct) |

`GetField` in the same file reads at `offset = field * 8`, so the reader shares
the emitter's 8-byte stride but not the allocator's packed model.

## Reachability

Wired, not dead code:
`src/compiler/80.driver/driver_pipeline_execution.spl:33,59`
-> `CodegenPipeline.jit()` -> `codegen.spl:297` -> `compile_inst` -> this arm.

## Why it has gone unnoticed

Every type that falls through `MirType.primitive_size()` — the five SIMD vector
types, plus `Slice`, `Struct`, `Enum`, `Opaque`, `ScalableVec`, `Promise`,
`Generator` — reports **8** from the residual `case _: 8`. That is exactly the
stride the emitter assumes, so the two independent defects **cancel** for
single-field aggregates and diverge silently as soon as there is more than one
field. Two bugs agreeing is not the same as either being right.

## Interaction — read before fixing either one

Fixing the SIMD residual **alone** makes this worse. Once `Vec4f` reports 16
while the emitter still strides 8, a case that is currently accidentally
consistent becomes inconsistent. **The stride and the size model must be
reconciled in the same change.**

## Limit of this record, stated rather than papered over

This is a static trace. The overflow has **not been executed and observed**. The
next step is a repro that constructs a 3-field tuple through the pure-Simple JIT
pipeline and compares the emitted stack-slot size against the store offsets.
That is not claimed here.

## Fix direction

Give `aggregate_type` the real aggregate type (or bypass it and compute the slot
from the operand types directly), then derive BOTH the slot size and the per-field
offsets from one layout function, so a stride can never disagree with the size
it is writing into.
