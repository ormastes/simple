# arm64 boot runtime: two incompatible TAG_FLOAT encodings

- Status: open
- Area: SimpleOS arm64 boot runtime (`examples/09_embedded/simple_os/arch/arm64/boot/`)
- Found: 2026-11-21, arm64 fs-exec kernel link lane (PR for `runtime_value_shims.spl`)

## Defect

The arm64 boot C runtime encodes a tagged float (TAG_FLOAT = 2) in two different ways:

| Site | Encoding |
|---|---|
| `value_runtime_owner.c:52-57` `any_box_f64`, `:41-49` `any_as_f64` | masked: `(bits & ~7) \| 2` |
| `baremetal_stubs.c:825` `rt_f64_to_bits` path, `:822-826` `f64_from_bits` | shifted: `(bits << 3) \| 2` |

The LLVM codegen boxes f64 with the **masked** form
(`src/compiler_rust/compiler/src/codegen/llvm/functions.rs:398-408`,
`((bits >> 3) << 3) | TAG_FLOAT`). A value produced by `f64_from_bits` therefore
decodes to a different number in `any_as_f64` (and in
`src/os/kernel/arch/arm64/runtime_value_shims.spl`). The shifted form also
loses IEEE bits 61-63, so it cannot round-trip `1.0`.

## Fix direction

Make `baremetal_stubs.c` `f64_from_bits` / `rt_f64_to_bits` use the masked
encoding that codegen and `value_runtime_owner.c` already use. Add a check that
round-trips `1.0`, `-0.0` and `1e300` through box and unbox.
