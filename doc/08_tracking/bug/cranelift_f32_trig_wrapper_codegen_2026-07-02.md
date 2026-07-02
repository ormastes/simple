# Cranelift JIT: f64→f32 trig wrapper bodies fail codegen (engine3d)

Date: 2026-07-02
Status: open (interpreter fallback works)
Severity: P3
Found by: W6 lane agent

## Symptom

```
JIT compilation failed ... Cranelift JIT compile: Module error: codegen:
7 function body/bodies failed to compile:
[_sin, _cos, _tan, _sqrt, gpu3d_sqrt_f32, gpu3d_sin_f32, gpu3d_cos_f32]
```

The Cranelift verifier rejects the f64→f32 trig wrapper bodies in
`src/lib/nogc_sync_mut/gpu/engine3d/` (math_hooks/simd_kernels3d).
Surfaced once earlier lowering blockers were cleared; engine3d programs
run interpreted until fixed.

Precise verifier error (W6b run):
`inst34 (v23 = fdemote.f32 v22): arg 0 (v22) with type i64 failed to
satisfy type set` — the FFI math shims return i64 where f32/f64 is
expected, so `fdemote` sees an integer. Root: extern return-type mapping
for the rt_math_* shims in codegen, not the .spl wrappers themselves.

## W6d expansion + performance consequence

The fallback set is larger than the 7 above: a W6d (game.rollball) run shows
the whole 3D transform/raster path falling back, 28 bodies:
`mat4_rotate_x/y/z, mat4_perspective, mat4_look_at, vec3_length,
vec3_normalize, _sin, _cos, _tan, _sqrt, gpu3d_{sqrt,sin,cos}_f32,
_emu3_{sin,cos,sqrt}, emu_draw_sphere, emu_draw_line_3d, emu_apply_ssr,
_shade_vertex, Vec2.length, Vec3.length, Mat4.perspective,
Quaternion.{from_axis_angle,length}, collide_sphere_aabb,
collide_sphere_capsule`. Because these are on the hot render path, the ENTIRE
engine3d CPU raster runs interpreted.

Measured consequence (game.rollball, 800x600, CpuBackend3D, this host under a
concurrent bootstrap): per-frame render p95 ≈ 2.9 s idle → 12–26 s under load,
versus the master-plan G4.x target of ≤ 33 ms — off by ~90–800×. The game ships
its evidence frames at 240x180 to stay runnable; the 33 ms target is
unreachable until this JIT fallback is fixed. No pure-Simple workaround exists
(the slowness is the interpreter, not the .spl code). Recorded as the perf gap
for W6d G4.x; fixing the extern return-type mapping should let the raster path
JIT-compile and close it.
