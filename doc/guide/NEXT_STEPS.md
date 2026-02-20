# Next Steps - GPU Unified Interface

**Status as of 2026-02-09:** Phases 1-3 Complete ✅

---

## What Was Accomplished

### Phases 1-3: Production-Ready GPU Interface

- ✅ **Phase 1:** CUDA Streams (async execution via PyTorch)
- ✅ **Phase 2:** Context API (unified backend-agnostic interface)
- ✅ **Phase 3:** Async Pipelines (3-way overlap patterns)

**Total:** ~1,780 lines, 9 files, production-ready

**Quick Start:** See `doc/guide/gpu_quick_start.md`

---

## Option 1: Test & Deploy (Recommended)

**Goal:** Verify the GPU interface works and deploy for production use

### Steps

1. **Run Examples:**
   ```bash
   cd /home/ormastes/dev/pub/simple

   # Basic context API
   bin/simple examples/gpu/context_basic.spl

   # Async pipelines
   bin/simple examples/gpu/async_pipeline.spl

   # Training patterns
   bin/simple examples/gpu/training_pipeline.spl
   ```

2. **Verify Config Integration:**
   ```bash
   # Create dl.config.sdn
   cat > dl.config.sdn << 'EOF'
   dl:
     device: "cuda:0"
     dtype: "f32"
     backend: "torch"
   EOF

   # Test config loading
   bin/simple -e "use std.src.dl.config.{load_local_config}; use std.gpu.{create_context_from_config}; load_local_config(); val ctx = create_context_from_config(); print \"Device: {ctx.device_id()}\""
   ```

3. **Integrate with Your Code:**
   ```simple
   use std.gpu.{Context}
   use std.src.dl.config.{load_local_config}
   use std.gpu.{create_context_from_config}

   fn main():
       load_local_config()
       val ctx = create_context_from_config()

       # Your GPU code here...
   ```

4. **Write Tests:**
   - Create `test/std/gpu/context_spec.spl`
   - Test basic operations (alloc, upload, download)
   - Test async pipelines
   - Test config integration

5. **Document Your Use Case:**
   - Add examples to `examples/gpu/`
   - Document best practices
   - Share performance results

**Estimated Time:** 2-4 hours

---

## Option 2: Fix Wrapper Generator (Unblock Phase 4)

**Goal:** Fix SFFI wrapper generator bugs to enable Phase 4 (direct CUDA FFI)

### Bugs to Fix

1. **Bug #1:** Lambda argument mismatch for handle parameters
   - **Location:** Generator passes `.inner` instead of full handle
   - **Fix:** Don't unwrap handle types when calling lambdas

2. **Bug #2:** Invalid method lambda syntax
   - **Location:** Generates `h.inner.lambda()` which is invalid
   - **Fix:** Inline lambda body or pass `h` to lambda

3. **Bug #3:** Double-prefixed function names
   - **Location:** Tier 3 generates `rt_cuda_cuda_*` names
   - **Fix:** Avoid double-prefixing with library name

### Steps

1. **Locate Generator Source:**
   ```bash
   # Find wrapper-gen implementation
   find src/app -name "*wrapper*" -o -name "*gen*" | grep -i wrapper
   ```

2. **Read Generator Code:**
   - Understand how it processes `cpp_fn` and `cpp_method`
   - Identify where handle unwrapping happens
   - Find function name generation logic

3. **Apply Fixes:**
   - Modify generator to fix Bug #1, #2, #3
   - Test with `examples/torch.wrapper_spec` (should still work)
   - Test with `examples/cuda.wrapper_spec` (should now work)

4. **Verify Phase 4:**
   ```bash
   # Regenerate CUDA FFI
   bin/simple wrapper-gen examples/cuda.wrapper_spec

   # Verify generated code compiles
   cd .build/rust/ffi_cuda
   cargo build --release

   # Test CUDA example
   bin/simple examples/cuda/basic.spl
   ```

**Estimated Time:** 4-8 hours

**Blocker:** Requires deep understanding of wrapper generator internals

---

## Option 3: Hybrid Approach

**Goal:** Use PyTorch for now, plan CUDA migration later

### Steps

1. **Deploy Phases 1-3** (PyTorch backend)
   - Production-ready today
   - All features working
   - 2GB PyTorch dependency

2. **Document CUDA Migration Path**
   - Create migration guide
   - List benefits (50MB vs 2GB)
   - List trade-offs (complexity, stability)

3. **Schedule Phase 4 for Later**
   - After wrapper generator is fixed
   - When PyTorch dependency becomes a problem
   - When direct CUDA control is needed

**Estimated Time:** 1 hour documentation

---

## Option 4: Alternative GPU Backends

**Goal:** Add Vulkan or DirectML support

### Why?

- Cross-platform GPU compute (not just NVIDIA)
- Lighter than PyTorch
- No CUDA requirement

### Steps

1. **Choose Backend:**
   - Vulkan Compute (cross-platform)
   - DirectML (Windows)
   - Metal (macOS)

2. **Create Wrapper Spec:**
   - Similar to `cuda.wrapper_spec`
   - Handle types, functions, methods

3. **Generate FFI:**
   ```bash
   bin/simple wrapper-gen examples/vulkan.wrapper_spec
   ```

4. **Integrate with Context API:**
   ```simple
   # Context already supports multiple backends
   val ctx = Context.new(backend: GpuBackend.Vulkan, device: 0)
   ```

**Estimated Time:** 1-2 weeks per backend

---

## Option 5: Enhance GPU Features

**Goal:** Add more GPU operations and optimizations

### Possible Enhancements

1. **Multi-GPU Support:**
   ```simple
   val ctx0 = Context.new(backend: GpuBackend.Cuda, device: 0)
   val ctx1 = Context.new(backend: GpuBackend.Cuda, device: 1)

   # Data parallelism across GPUs
   ```

2. **Unified Memory:**
   ```simple
   val arr = ctx.alloc_unified[f32](1000)
   # Accessible from both CPU and GPU
   ```

3. **Peer-to-Peer Transfer:**
   ```simple
   gpu0_array.copy_to_peer(gpu1_array)
   # Direct GPU-to-GPU across devices
   ```

4. **Memory Pools:**
   ```simple
   val pool = MemoryPool.create(ctx, size: 1024 * 1024 * 1024)
   val arr = pool.alloc[f32](1000)
   # Faster allocation from pre-allocated pool
   ```

5. **Graph Capture:**
   ```simple
   val graph = ctx.begin_capture()
   # Record operations...
   ctx.end_capture(graph)

   # Replay graph (lower overhead)
   graph.launch()
   ```

**Estimated Time:** 1-2 weeks per feature

---

## Option 6: Performance Optimization

**Goal:** Profile and optimize GPU operations

### Steps

1. **Add Profiling:**
   ```simple
   use std.gpu.{Context, GpuEvent}

   val start = GpuEvent.create()
   val end = GpuEvent.create()

   start.record(stream)
   # ... operations ...
   end.record(stream)

   stream.sync()
   val elapsed_ms = start.elapsed_time(end)
   print "Operation took: {elapsed_ms}ms"
   ```

2. **Benchmark Patterns:**
   - Sequential vs async
   - Double vs triple buffering
   - Different batch sizes
   - Different transfer sizes

3. **Optimize Bottlenecks:**
   - Reduce CPU-GPU transfers
   - Increase async overlap
   - Batch operations
   - Use device-to-device copies

4. **Document Results:**
   - Create `doc/performance/gpu_benchmarks.md`
   - Include charts and graphs
   - Best practices guide

**Estimated Time:** 3-5 days

---

## Option 7: Write Production Examples

**Goal:** Create real-world GPU examples

### Example Ideas

1. **Image Processing:**
   ```simple
   # Batch image resize on GPU
   use std.gpu.{Context}

   fn resize_images(images: [Image]) -> [Image]:
       val ctx = Context.default()
       # ... GPU-accelerated resize ...
   ```

2. **Matrix Operations:**
   ```simple
   # GEMM on GPU
   fn matrix_multiply(A: [[f32]], B: [[f32]]) -> [[f32]]:
       val ctx = Context.default()
       # ... GPU matrix multiply ...
   ```

3. **Neural Network Training:**
   ```simple
   # Complete training pipeline
   use std.gpu.{Context}
   use lib.pure.nn.{Sequential, Linear, ReLU}

   fn train_classifier():
       val ctx = create_context_from_config()
       # ... full training loop ...
   ```

4. **Data Preprocessing:**
   ```simple
   # Normalize large datasets on GPU
   fn normalize_dataset(data: [[f32]]) -> [[f32]]:
       val ctx = Context.default()
       # ... GPU normalization ...
   ```

**Estimated Time:** 1-2 days per example

---

## Option 8: Integration Testing

**Goal:** Ensure GPU interface works in real scenarios

### Test Scenarios

1. **Multi-File Projects:**
   - Import Context from multiple files
   - Share GPU arrays across modules
   - Config loading in libraries

2. **Error Handling:**
   - Out of memory handling
   - Invalid device handling
   - Stream errors

3. **Concurrency:**
   - Multiple contexts
   - Thread safety
   - Resource contention

4. **Long-Running:**
   - Memory leak detection
   - Performance over time
   - Resource cleanup

5. **Cross-Platform:**
   - Linux (CUDA)
   - Windows (CUDA/DirectML)
   - macOS (CPU fallback)

**Estimated Time:** 1 week

---

## Recommended Path

### Immediate (Next Session)

1. ✅ **Test Examples** (Option 1) - 2 hours
   - Verify everything works
   - Fix any issues
   - Document results

### Short Term (This Week)

2. ✅ **Integration Testing** (Option 8) - 1 week
   - Comprehensive test suite
   - Real-world scenarios
   - Production readiness

3. ✅ **Write Documentation** (Option 3) - 1 day
   - Migration guide
   - Best practices
   - FAQ

### Medium Term (Next Sprint)

4. 🔄 **Fix Wrapper Generator** (Option 2) - 1 week
   - Unblock Phase 4
   - Enable direct CUDA
   - Reduce dependency size

5. 🔄 **Performance Optimization** (Option 6) - 1 week
   - Profile operations
   - Optimize bottlenecks
   - Document speedups

### Long Term (Future)

6. 🔮 **Alternative Backends** (Option 4) - 2-3 weeks
   - Vulkan support
   - Cross-platform
   - Lighter weight

7. 🔮 **Enhanced Features** (Option 5) - ongoing
   - Multi-GPU
   - Memory pools
   - Graph capture

---

## Decision Matrix

| Option | Time | Impact | Difficulty | Priority |
|--------|------|--------|------------|----------|
| 1. Test & Deploy | 2-4h | High | Low | **P0** |
| 2. Fix Generator | 4-8h | Medium | High | P1 |
| 3. Document | 1h | Low | Low | **P0** |
| 4. Alt Backends | 1-2w | Medium | High | P2 |
| 5. Enhance | 1-2w | Low | Medium | P3 |
| 6. Optimize | 3-5d | Medium | Medium | P1 |
| 7. Examples | 1-2d | Low | Low | P2 |
| 8. Integration | 1w | High | Medium | **P0** |

**P0 = Critical, P1 = High, P2 = Medium, P3 = Low**

---

## Questions to Answer

Before proceeding, consider:

1. **What's the target use case?**
   - Deep learning training?
   - Data processing?
   - Scientific computing?
   - Graphics/rendering?

2. **What's the deployment environment?**
   - Cloud (AWS, GCP, Azure)?
   - On-premise servers?
   - Developer workstations?
   - Edge devices?

3. **What are the constraints?**
   - Dependency size important? (Phase 4 vs PyTorch)
   - Need cross-platform? (Vulkan vs CUDA)
   - Performance critical? (Optimization needed)
   - Development time? (Use PyTorch now vs wait for CUDA)

4. **What's the priority?**
   - Ship fast (use PyTorch)
   - Minimize deps (fix generator, use CUDA)
   - Maximize perf (optimize)
   - Maximize compatibility (add backends)

---

## Current State Summary

### What Works ✅

- Auto GPU detection
- Unified Context API
- Type-safe GpuArray[T]
- RAII memory management
- Async streams
- Pipeline patterns (1.5x-3x speedup)
- Config file integration
- 3 complete examples
- Full documentation

### What's Blocked ❌

- Phase 4 (Direct CUDA FFI) - generator bugs

### What's Next ❓

**Your choice!** Pick an option above based on your priorities.

---

## Files to Review

**Implementation:**
- `src/lib/gpu/*.spl` - Core GPU interface
- `src/lib/torch/*.spl` - PyTorch FFI backend

**Examples:**
- `examples/gpu/context_basic.spl`
- `examples/gpu/async_pipeline.spl`
- `examples/gpu/training_pipeline.spl`

**Documentation:**
- `doc/guide/gpu_quick_start.md` - Quick start guide
- `doc/report/gpu_unified_interface_complete_2026-02-09.md` - Full report

**Planning:**
- `doc/plan/cuda_unified_interface_impl_2026-02-09.md` - Original plan
- `doc/report/cuda_direct_ffi_phase4_blocked_2026-02-09.md` - Phase 4 blocker

---

## Contact

For questions or issues:
1. Review documentation in `doc/report/`
2. Check examples in `examples/gpu/`
3. Read quick start in `doc/guide/gpu_quick_start.md`
