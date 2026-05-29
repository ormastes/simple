<!-- codex-design -->
# Graphics Backend Acceleration System Test Plan

Date: 2026-05-16
Status: Candidate plan pending requirement selection

## Test Categories

1. CPU-only default:
   - backend auto-detect returns CPU/software when no GPU feature is enabled;
   - strict CPU creation passes;
   - strict GPU creation reports typed unavailable.

2. No silent fallback:
   - requesting `cuda`, `vulkan`, `metal`, or `webgpu` in strict mode must not return CPU.

3. Hardware parity:
   - clear, filled rect, blit, clip, and readback match CPU reference.

4. Feature build linkage:
   - default runtime builds without GPU dependencies;
   - `cuda`, `vulkan`, and `webgpu-real` resolve expected runtime symbols.

5. SIMD:
   - scalar and SIMD CPU paths match;
   - target features are reported;
   - unrelated `rt_simd_*` externs are not linked.

6. Direct C vs Simple 2D:
   - shared fixtures render the same pixel hash or approved diff;
   - report p50/p95 and `simple_vs_c_ratio`.

7. Simple GUI app vs Rust+Tauri:
   - startup, new window, close, resize, scroll, route change, IPC, event broadcast, idle memory;
   - report Tauri renderer identity and Simple backend identity;
   - fail Tauri-equivalent performance claim when selected NFR ratios are missed.

8. Chrome vs Simple web rendering:
   - static, scroll, route, selector, canvas/WebGPU fixtures;
   - compare pixel output plus timing;
   - report FPS/dropped-frame/GPU-raster status when Chrome exposes it.

9. Window-manager optimization:
   - no production tight present loop;
   - idle CPU budget;
   - frame pacing p95;
   - dirty-rect redraw area versus full-frame redraw area.

## Required Evidence

Backend smokes record:

- requested backend;
- selected backend;
- device name;
- feature gate;
- shader format;
- init time;
- command time;
- readback time;
- max RSS if available;
- fallback reason when unavailable.

Performance reports additionally record:

- reference kind: `c`, `chrome`, or `rust-tauri`;
- Simple mode: interpreter, native, LLVM, CPU scalar, CPU SIMD, CUDA, Vulkan, Metal, or WebGPU;
- sample count and warmup count;
- p50/p95/p99;
- ratio against reference;
- active Simple optimization providers;
- pixel hash or diff status;
- PASS/WARN/FAIL reason.

