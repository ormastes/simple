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
