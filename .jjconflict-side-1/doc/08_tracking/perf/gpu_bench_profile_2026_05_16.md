# GPU Benchmark Hotspot Profile — 2026-05-16

## Setup
- Scene: fill_1080p (clear + 100 rects), 1920x1080 RGBA, 100 timed frames
- GPU: NVIDIA RTX A6000 / sm_75 PTX
- Simple interpreter with HashMap extern dispatch + pre-allocated launch buffers

## Head-to-Head

| Metric | C (native) | Simple (interpreter) | Ratio |
|--------|-----------|---------------------|-------|
| avg/frame | **300 us** | **2,414 us** | 8.0x |
| Mpix/s | 6,921 | 859 | 8.1x |

## Micro-Benchmark Results

| Operation | Time | Notes |
|-----------|------|-------|
| `rt_ptr_write_i64` (extern dispatch) | **1.87 us/call** | Actual work: ~1ns (memory store) |
| Arithmetic iteration (mul, mod, add, cmp, assign) | **3.38 us/iter** | Interpreter eval overhead |
| Function call + extern (fn wrapper) | **3.83 us/call** | Extra ~1.96 us vs bare extern |

## Per-Frame Cost Breakdown (2,414 us total)

| Component | Calls/frame | Cost | % of frame |
|-----------|------------|------|------------|
| **rt_ptr_write_i64 dispatch** | 502 | ~939 us | **39%** |
| **Function call overhead** (scope creation, arg passing) | ~201 | ~394 us | **16%** |
| **Arithmetic interpreter loop** (scene rect params) | ~100 iters | ~338 us | **14%** |
| **GPU actual work** (101 launches + sync) | 102 | ~300 us | **12%** |
| **CUDA extern dispatch** (launch_kernel, sync) | 102 | ~191 us | **8%** |
| **Loop control + var lookup** | — | ~252 us | **11%** |

## Hotspot Analysis

### #1: rt_ptr_write_i64 dispatch — 39% (939 us)
Each frame writes 502 values to pre-allocated param buffers (5 per rect × 100 rects + 2 for clear).
The actual work is a single memory store (~1 ns). The interpreter adds **1,870x overhead** per call:
- HashMap lookup for extern name
- Value::Int unboxing for 3 arguments
- Result boxing (Value::Int)
- Scope/stack management

**Fix:** JIT-compile the scene loop. All 502 ptr_writes become native `mov [addr], val` instructions.

### #2: Function call overhead — 16% (394 us)
201 Simple function calls per frame (launch_clear, launch_rect×100, fill_color×100, scene_fill_1080p).
Each adds ~1.96 us over a bare extern call: scope allocation, argument binding, return value propagation.

**Fix:** JIT compilation eliminates scope allocation entirely. Alternatively: inline launch helpers into the scene loop.

### #3: Arithmetic interpreter loop — 14% (338 us)
100 iterations of scene_fill_1080p compute rect params (mul, mod, add, compare, branch).
At 3.38 us/iter, this is ~3,380x slower than native arithmetic (~1 ns/op).

**Fix:** JIT-compile the loop body. All arithmetic becomes native x86 instructions.

### #4: GPU work — 12% (300 us) — IRREDUCIBLE
This is the actual GPU kernel execution time (same in C and Simple).
Cannot be reduced by interpreter optimizations.

### #5: CUDA extern dispatch — 8% (191 us)
102 calls to rt_cuda_launch_kernel/sync. Similar overhead to ptr_write but these
calls also do real GPU work, so the dispatch overhead is proportionally smaller.

**Fix:** JIT + batch launches (single kernel with rect array instead of 100 separate launches).

## Optimization Path Priority

| Priority | Optimization | Expected Gain | Effort |
|----------|-------------|---------------|--------|
| **P0** | JIT scene loop (ptr_writes + arithmetic become native) | -1,671 us (69%) → ~743 us/frame | High |
| P1 | Inline launch helpers (eliminate fn call overhead) | -394 us (16%) | Low |
| P2 | Batch kernel launch (1 launch for all rects) | -180 us (GPU launch overhead) | Medium |
| P3 | Further interpreter opts (scope pooling, Value unboxing) | -100 us (4%) | Medium |

## Theoretical Minimum (all optimized)
- JIT scene loop: ~300-330 us (1.0-1.1x C, GPU-bound)
- Post-JIT, host-side overhead collapses to native cost: Cranelift emits identical
  call/ret ABI, register-passed args, and native x86 arithmetic. The interpreter
  dispatch, Value boxing, and scope allocation all disappear entirely.
- Only delta from C: JIT compile-once cost (amortized over 100+ frames → negligible)
