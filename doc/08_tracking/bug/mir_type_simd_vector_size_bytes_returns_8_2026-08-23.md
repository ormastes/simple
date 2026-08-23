# MirType.size_bytes() returns 8 for every SIMD vector type (should be 16 or 32)

- **Filed:** 2026-08-23
- **Status:** OPEN — RED test landed, source deliberately not modified
- **Severity:** HIGH — silent wrong layout value
- **Source:** `src/compiler/50.mir/mir_types.spl`
- **Test (RED):** `test/01_unit/compiler/mir/mir_construct_matrix_spec.spl`,
  describe block "MirTypeKind SIMD vector layout values (RED — filed defect)"
  (mirrored in `test/unit/...`)

## Summary

`MirType.primitive_size()` (`mir_types.spl:229`) has no arm for the five SIMD
vector variants, so `size_bytes()` and `alignment()` both fall through to their
residual `case _: 8`. Every SIMD vector type reports **8 bytes, 8-byte aligned**.

`mir_types.spl` documents the intended widths on the variants themselves:

```
    Vec4f     # 4x f32 (128-bit SSE/NEON)
    Vec8f     # 8x f32 (256-bit AVX2)
    Vec4d     # 4x f64 (256-bit AVX2)
    Vec4i     # 4x i32 (128-bit SSE/NEON)
    Vec8i     # 8x i32 (256-bit AVX2)
```

| type | documented width | `size_bytes()` | `alignment()` |
|---|---|---|---|
| `Vec4f` | 128-bit = 16 | **8** | **8** (want 16) |
| `Vec4i` | 128-bit = 16 | **8** | **8** (want 16) |
| `Vec8f` | 256-bit = 32 | **8** | **8** (want 32) |
| `Vec4d` | 256-bit = 32 | **8** | **8** (want 32) |
| `Vec8i` | 256-bit = 32 | **8** | **8** (want 32) |

## Why this matters

This is the session's characteristic defect class: it does not fault, it returns
a number, and the number is wrong. Any consumer computing a stack slot, an array
stride, a struct offset, or an alignment for a SIMD local gets a slot 2-4x too
small. Nested aggregates compound it — `size_bytes()` recurses through `Array`,
`Tuple` and `Union`, so a `[(Vec4f, Vec4f); 8]` is off by 128 bytes with no
diagnostic anywhere.

It also interacts with the fail-open backends
(`mir_constructs_silently_dropped_by_fail_open_backends_2026-08-23.md`): the SIMD
*instructions* are silently dropped by all five, and the SIMD *types* are
silently mis-sized, so nothing in the pipeline objects.

## Fix direction

Add the arm to `primitive_size()` — or, if these are deliberately handle-sized
in some lowering, say so explicitly in `size_bytes()` with its own arm and a
comment, rather than letting them fall into an unrelated residual case. Silence
is the bug as much as the number is.

---

## Blast-radius determination (added 2026-08-23, second pass)

**Question asked:** is this contained to vector types, or does it reach general
layout/allocation/offset computation?

**Answer: it reaches general layout — and the general-layout defect is WORSE than
the SIMD one and does not depend on it.**

### Consumers

23 owned non-test call sites of `.size_bytes()`. The load-bearing ones are
allocation sites, not SIMD sites:

| site | use |
|---|---|
| `src/compiler/70.backend/codegen.spl:348` | `case Alloc(dest, type_)` — **general stack allocation size** |
| `src/compiler/70.backend/codegen.spl:376` | `case Aggregate(...)` — **stack slot for every struct/tuple/enum/array construction** |
| `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:1196,1221,1238,1460` | cast width selection and `operand_size` |
| `isel_x86_64 / isel_aarch64 / isel_riscv64 / isel_riscv32` | 2 sites each |

None of these is SIMD-specific. `Alloc` and `Aggregate` are the generic paths.

### The larger defect found while tracing it

`codegen.spl` `case Aggregate` (live path: `driver_pipeline_execution.spl:33,59`
-> `CodegenPipeline.jit()` -> `compile_inst` -> this arm):

```
val type_ = self.aggregate_type(kind)
val size  = type_.size_bytes()
val slot  = cranelift_stack_slot(self.current_ctx, size, 8)
var offset = 0
for operand in operands:
    ... cranelift_store(self.current_ctx, v, addr, 0)
    offset = offset + 8          # "Assume 8 bytes per element"
```

and `aggregate_type` (`codegen.spl:585`) discards the real type before
`size_bytes()` is ever called:

```
case Array(type_): type_                      # the ELEMENT type, not the array
case Tuple:        MirType(kind: MirTypeKind.I64)
case Struct(_):    MirType(kind: MirTypeKind.I64)
case Enum(_, _):   MirType(kind: MirTypeKind.I64)
```

So the slot is sized **8 bytes** for every `Tuple`, `Struct` and `Enum`
aggregate, and **one element wide** for every `Array`, while the write loop
advances 8 bytes per operand. For any aggregate with N operands the stores run
to offset `8*(N-1)`, i.e. **a stack slot overflow of `8*(N-1)` bytes on every
multi-field struct, tuple or enum-payload construction**, and `8*N - elem_size`
for arrays. `GetField` in the same file compounds the disagreement by reading at
`field * 8`, a stride the packed `size_bytes()` model does not share.

Two incompatible size models coexist in this path: `size_bytes()` computes a
**packed sum** (`(I8,I32,I64)` = 13), while the emitter assumes a **uniform
8-byte stride** (= 24 for the same tuple).

### Why nothing has complained

The SIMD residual `case _: 8` and the hardcoded 8-byte stride **agree with each
other by accident**. Every type that falls through `primitive_size()` — the five
vector types, and also `Slice`, `Struct`, `Enum`, `Opaque`, `ScalableVec`,
`Promise`, `Generator` — reports 8, which is exactly the stride the emitter
assumes. The two bugs cancel for the single-field case and diverge silently as
soon as an aggregate has more than one field or a vector is stored by value.

### Verdict

- **Not contained to vector types.** The SIMD residual is one instance of a
  general "assume 8 bytes" pattern in the live pure-Simple JIT codegen path.
- The SIMD fix alone (adding the `primitive_size()` arm) would make things
  **worse before better**: `Vec4f` would start reporting 16 while the emitter
  still strides 8, so a currently-accidentally-consistent case becomes
  inconsistent. **The stride and the size model must be reconciled in the same
  change.**
- **Limit of this determination, stated rather than papered over:** this is a
  static read of a wired path (`driver_pipeline_execution.spl` -> `CodegenPipeline.jit()`).
  The overflow has **not been executed and observed**. A repro would construct a
  3-field tuple through the pure-Simple JIT pipeline and inspect the emitted
  stack slot size against the store offsets. That execution is the next step and
  is not claimed here.

**Filed severity raised from HIGH to CRITICAL** on the general-layout finding.
Recommend a separate record for the aggregate stride/size disagreement; it is a
different defect from the SIMD residual and should not be closed by fixing this
one.
