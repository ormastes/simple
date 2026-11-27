# opencl_backend_contract_spec: 5 failures (PLUG-E-NOTFOUND + SIMD types) — 2026-11-13

Status: fixed on `work/opencl-contract-20261113` (base `release/1.0.0` @ `164eea76b97`).
Host: aarch64 DGX Spark. No OpenCL hardware or driver is involved: every row is
source-generation / contract evidence.

## Symptom

`test/01_unit/compiler/codegen/opencl_backend_contract_spec.spl`: 14/19 passed.

| row | message |
|---|---|
| compiles tagged OpenCL kernels through the shared Codegen factory interface | `panic: PLUG-E-NOTFOUND: backend=opencl` |
| builds generated Engine2D OpenCL C to SPIR-V artifact evidence | `missing-entry-symbol:simple_2d_bitmap_glyph_raster_u32` |
| maps Simple SIMD vector types to OpenCL C vector types | `expected char to equal float4` |
| emits OpenCL C SIMD vector arithmetic and f32x4 reductions | params emitted as `char` |
| emits OpenCL C generic MirSimd vector operations | params emitted as `char` |

## Root causes (three, independent)

1. **PLUG-E-NOTFOUND: stale spec.** `CodegenFactory.create` selects from the
   *installed* static backend table. The default K1 table is an unselected stub
   (270ab10e40a), so with no composition root every request is NotFound. OpenCL
   is a P-static plugin (`plugins.backend_registry.full_static_backend_registry`).
   The row now lives in `opencl_codegen_factory_spec.spl`, which installs the
   llvm-cranelift K1 table plus the full P-static table, exactly like
   `backend_port_negotiate_spec`. It was split out because loading the registry
   also loads `plugins.backend_opencl.opencl_backend`, whose `OpenClBackend`
   shares a bare name with `compiler.backend.backend.opencl_backend`'s; the seed
   then reports `ambiguous type OpenClBackend ... none of them is imported by
   <entry>` for every other row (entry-module imports are not consulted by
   `resolve_class_in_scope`'s owner walk — open, see below).
2. **Glyph-raster row: stale fixture.** The generated Engine2D required-symbol
   set gained `simple_2d_bitmap_glyph_raster_u32`; the hip / gpu_generated_2d /
   generated_kernel_dispatch specs were updated, this one was not. The positive
   fixture now exports all five entries; the negative row is unchanged.
3. **SIMD rows: seed interpreter bug.** Inside a named fn body,
   `MirTypeKind.Vec4f` hit the module-style field-access shortcut in
   `src/compiler_rust/compiler/src/interpreter/expr/calls.rs`
   (`Expr::FieldAccess`, receiver identifier not in env): `Vec4f` is also a
   loaded class (`struct Vec4f` in std simd / `30.types/simd_vector_types.spl`),
   so it returned `<constructor:Vec4f>`. `Vec16f` (no such class) was fine.
   The `match` in `OpenClBackend.opencl_type` then took its first arm
   (`I8 -> "char"`). Fix: skip the function/class shortcut when the receiver
   names an enum that declares `field` as a variant, so the `EnumType` arm
   resolves it. Regression: `test/01_unit/language/enum_variant_shadows_class_name_spec.spl`.

The three SIMD rows go green only on a seed built from this change; the
pre-change seed still fails them.

## Evidence (aarch64, serial, 16G/900s cap per spec)

- Red: task seed `seedhead/simple` (src `517f20ae777`) on the unmodified spec:
  `passed=14 failed=5` (the five rows above).
- Baseline seed built from unmodified `164eea76b97` (sha256 `c5de1d4b...`),
  spec fixes applied: opencl contract `passed=15 failed=3` (SIMD rows), factory
  spec `1/1`, regression spec `1/2` (red on the fn-body row).
- Fixed seed (sha256 `2f0f7aec...`): opencl contract `18/18`, factory `1/1`,
  regression `2/2`.
- Neighbours unchanged base vs fixed: opencl_session_contract 8/8,
  gpu_generated_2d 2/2, group_algorithms 21/21, hip_backend 5/5,
  spec_constants 13/13, backend_gpu_target 8/8, backend_port_negotiate 7/7,
  call_origin_plugins 9/9, wildcard_import_codegen_factory 1/1; pre-existing
  reds identical on both: storage_simd_opencl (load error), subgroup_intrinsics
  23/24, vec_types_contract 18/22.

## Open follow-ups (not fixed here)

- A `match` on a `Value::Constructor` against unit-variant patterns silently
  takes the first arm instead of failing — that is what turned this into wrong
  output rather than an error.
- `resolve_class_in_scope` does not walk the `<entry>` module's own `use`
  bindings, so a spec that imports one of two same-named classes still sees
  them as ambiguous.
- `src/compiler/70.backend/backend/opencl_backend.spl` and
  `src/plugins/backend_opencl/opencl_backend.spl` are diverged duplicates.
