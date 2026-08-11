# Interpreter: Engine2D CPU-lane draw-op mutations lost → blank/uniform frames (Metal unaffected)

- **Date:** 2026-08-11
- **Severity:** high (CPU/software Engine2D rendering is silently wrong under the interpreter; showcase evidence gates fail)
- **Area:** src/lib/gc_async_mut/gpu/engine2d (Engine2D `me`-method delegation to nested backend class fields), seed interpreter receiver-mutation write-back

- **Status:** FIXED 2026-08-12 — explicit receiver write-backs added to all
  cpu/trait dispatch arms in engine.spl (42 cpu arms, 43 trait arms).

## Symptom
`graphics_2d_showcase_gui.spl` at 320x240 under the rust gui driver (interpreter lane):

| backend | checksum | semantic_differences | gate |
|---|---|---|---|
| metal | 951541957 | 4 | pass (device_readback) |
| cpu_simd | 153000 | 0 | fail (uniform clear-color frame) |
| software (create_offscreen) | 0 | 0 | fail (all-zero frame) |

Minimal repro: `scratchpad/cpu_lane_probe.spl` —

```
var cs = Engine2D.create_with_backend_fast(64, 64, "cpu_simd")
cs.clear(0xFF000000u32)                       # lands (native buffer side effect)
cs.draw_rect_filled(4, 4, 40, 20, 0xFF0000FFu32)  # LOST under interpreter
# readback: inside_rect == outside_rect == 4278190080 (0xFF000000) — rect never landed
# create_offscreen variant: even clear() is lost — every pixel reads 0
```

Metal passes because its draws are GPU-handle side effects; CPU/software backends
keep pixels in inline Simple buffers on nested class fields, and those mutations
never make it back.

## Mechanism
`Engine2D.draw_rect_filled` (engine.spl:1059) is a `me` method that dispatches to
a nested class field via a pattern binding without explicit write-back
(`elif val Some(vulkan) = self.vulkan_backend: vulkan.draw_rect_filled(...)` — the
cpu/software arms are the same shape). Under the interpreter, mutations the callee
makes to its own receiver (the nested backend object) are dropped — either the
`val Some(x)` binding copies the class value, or receiver write-back through the
nested field path is not honored. Same op under native execution is bit-exact
(check-cpu-simd-engine2d-evidence passes), so this is an interpreter-only
semantics divergence. Related: interp_cross_module_struct_field_collision_2026-07-04,
interp_env_get_name_collision_nil_root_2026-07-26.

Note `create_with_backend` (non-`fast`) additionally returned a **nil** engine
under the interpreter in the probe (`method draw_rect_filled not found on type
nil`) — possibly a second, constructor-side instance of the same class.

## Consequence
Any interpreted GUI/web render through the CPU lane produces background-only or
all-zero frames; the `SIMPLE_GUI_BACKEND=cpu_simd|software` showcase evidence
cannot pass interpreted. Metal windowed showcase is the only working CPU-free
lane today. Also masks event-evidence collection on CPU backends.

## Fix applied + verification (2026-08-12)
engine.spl cpu and trait arms now write the mutated receiver back
(`self.cpu_backend = Some(cpu); self.backend = cpu` / local `trait_backend`
write-back), 85 arms across all draw/state/read ops. Verified interpreted:
- probe `scratchpad/cpu_lane_probe.spl`: inside_rect=0xFF0000FF, outside=clear
  color on BOTH offscreen and cpu_simd (pre-fix: 0 / clear-only).
- showcase 320x240, gui driver, terminal:
  - cpu_simd: checksum=1103106534, semantic_differences=4 → PASS (was 153000/0)
  - software: checksum=1103106534, semantic_differences=4 → PASS (was 0/0)
  - cpu_simd ≡ software bit-identical — the SIMD/scalar bit-exactness contract
    holds in the interpreter lane too now.
- metal (trait arm path) unaffected: GPU-handle side effects always landed;
  regression re-run confirmed separately.

The interpreter-side root cause (receiver mutations through pattern-bound
nested class fields being dropped) remains OPEN in the seed interpreter — the
engine.spl write-backs are the workload-side fix; the compiler-side fix is
still fix direction #1 below.

## Fix direction
1. Interpreter: honor receiver mutation for methods invoked on pattern-bound
   nested class fields (or diagnose loudly instead of silently dropping).
2. Until then, Engine2D cpu/software arms should explicitly write back
   (`self.cpu_backend = cpu; self.backend = cpu`) like the cuda arm already does —
   cheap, semantics-preserving under native.
3. Add an interpreter-mode SPipe spec: clear+rect on software/cpu_simd must
   produce non-uniform readback (probe above as the fixture).
