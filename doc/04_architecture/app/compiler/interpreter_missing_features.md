# Interpreter Missing Features - Analysis

**Date:** 2026-02-06
**Question:** What additional features are needed to run all tests/examples not designed for interpreter?

## Executive Summary

To run **all tests and examples**, the interpreter needs **8 major feature categories**:

| Category | Status | Examples Blocked | Priority |
|----------|--------|------------------|----------|
| **1. MIR Serialization** | ⚠️ Placeholder | JIT compilation | **P0** (Critical) |
| **2. Unsafe Code** | ❌ Not implemented | Bare-metal, FFI | **P0** (Critical) |
| **3. Inline Assembly** | ❌ Not implemented | Bare-metal, SIMD | **P1** (High) |
| **4. Async/Await** | ⚠️ Partial | Async examples | **P1** (High) |
| **5. FFI Type Marshaling** | ⚠️ Partial (i64 only) | External libs | **P1** (High) |
| **6. SIMD/GPU** | ❌ Not implemented | GPU patterns | **P2** (Medium) |
| **7. Parallel Execution** | ❌ Not implemented | Parallel I/O | **P2** (Medium) |
| **8. No-Std/Bare-Metal** | ❌ Not implemented | Embedded | **P3** (Low) |

**Current Coverage:**
- ✅ **Can run:** ~60% of examples (standard Simple code)
- ⚠️ **Partial:** ~20% (limited by type marshaling, async)
- ❌ **Cannot run:** ~20% (bare-metal, GPU, SIMD)

## Detailed Analysis

### 1. MIR Serialization ⚠️ (P0 - Critical)

**Status:** Placeholder (commented code)

**Blocks:** JIT compilation for all functions

**Example:** `src/compiler/backend/jit_interpreter.spl:181`
```simple
# Step 2: Serialize MIR to string
# NOTE: This is the missing piece - MIR serialization
# TODO: Implement serialize_mir_to_json(mir_fn) or serialize_mir_to_binary(mir_fn)
if self.config.mode == JitMode.AlwaysJit:
    return Err(BackendError.not_implemented(
        "MIR serialization not yet implemented - cannot JIT compile"
    ))
```

**What's Needed:**

```simple
# JSON Serialization (easier to debug)
fn serialize_mir_to_json(mir: MirFunction) -> text:
    """Serialize MIR to JSON for JIT compilation."""
    var json = "{"
    json += "\"name\": \"{mir.name}\","
    json += "\"params\": ["
    for param in mir.params:
        json += "{\"type\": \"{param.ty}\"},"
    json += "],"
    json += "\"body\": ["
    for inst in mir.body:
        json += serialize_mir_instruction(inst)
    json += "]"
    json += "}"
    json

# Binary Serialization (faster)
fn serialize_mir_to_binary(mir: MirFunction) -> [u8]:
    """Serialize MIR to binary for faster JIT compilation."""
    var bytes: [u8] = []

    # Magic number
    bytes = bytes.append([0x4D, 0x49, 0x52, 0x00])  # "MIR\0"

    # Name length + name
    bytes = bytes.append(encode_string(mir.name))

    # Param count + params
    bytes = bytes.append(encode_i32(mir.params.len()))
    for param in mir.params:
        bytes = bytes.append(encode_type(param.ty))

    # Instruction count + instructions
    bytes = bytes.append(encode_i32(mir.body.len()))
    for inst in mir.body:
        bytes = bytes.append(encode_mir_instruction(inst))

    bytes
```

**Impact:** Enables full JIT compilation for **all functions**

**Workaround:** Falls back to tree-walking interpretation (current behavior)

**Estimated Effort:** 2-3 days

---

### 2. Unsafe Code ❌ (P0 - Critical)

**Status:** Not implemented

**Blocks:** Bare-metal examples, low-level FFI, SIMD

**Example:** `examples/baremetal/hello_x86.spl:24-28`
```simple
unsafe:
    # Write character
    *(addr as ptr<u8>) = ch
    # Write color attribute
    *((addr + 1) as ptr<u8>) = color
```

**What's Needed:**

1. **Unsafe Blocks**
   ```simple
   fn vga_put_char(addr: u32, ch: u8):
       unsafe:
           *(addr as ptr<u8>) = ch  # Raw pointer write
   ```

2. **Raw Pointer Operations**
   ```simple
   # Dereference (read)
   val value = *ptr

   # Dereference (write)
   *ptr = 42

   # Pointer arithmetic
   val next = ptr + 1
   val prev = ptr - 1

   # Pointer casting
   val u8_ptr = addr as ptr<u8>
   val u32_ptr = addr as ptr<u32>
   ```

3. **Pointer Types**
   ```simple
   val raw_ptr: ptr<u8>           # Raw pointer
   val const_ptr: const ptr<i32>  # Const pointer
   val mut_ptr: mut ptr<u32>      # Mutable pointer
   ```

**Implementation Strategy:**

```simple
# In interpreter backend
impl InterpreterBackendImpl:
    fn eval_expr(expr: HirExpr, ctx: EvalContext) -> Result<Value, BackendError>:
        match expr.kind:
            case Unsafe(body):
                # Enter unsafe mode
                ctx.enter_unsafe()
                val result = self.eval_block(body, ctx)?
                ctx.exit_unsafe()
                Ok(result)

            case Deref(ptr_expr):
                if not ctx.is_unsafe():
                    return Err(BackendError.type_error(
                        "dereference requires unsafe block", Some(expr.span)
                    ))

                val ptr_val = self.eval_expr(ptr_expr, ctx)?
                match ptr_val:
                    case RuntimeValue(ptr):
                        # Read from memory via FFI
                        val value = rt_memory_read(ptr)
                        Ok(value)
                    case _:
                        Err(BackendError.type_error("not a pointer", Some(expr.span)))

            case PointerCast(expr, target_ty):
                val value = self.eval_expr(expr, ctx)?
                # Reinterpret as different pointer type
                Ok(value)  # No-op at runtime
```

**FFI Support:**
```simple
# In src/app/io/mod.spl
extern fn rt_memory_read_u8(addr: i64) -> u8
extern fn rt_memory_read_u32(addr: i64) -> u32
extern fn rt_memory_write_u8(addr: i64, value: u8)
extern fn rt_memory_write_u32(addr: i64, value: u32)
```

**Impact:** Enables bare-metal programming, low-level FFI

**Estimated Effort:** 3-5 days

---

### 3. Inline Assembly ❌ (P1 - High)

**Status:** Parser supports syntax, but no execution

**Blocks:** Bare-metal, SIMD optimizations, crypto

**Example:** `examples/baremetal/hello_x86.spl:48-53`
```simple
@naked
fn halt():
    asm:
        "cli"           # Disable interrupts
        ".loop:"
        "hlt"           # Halt CPU
        "jmp .loop"     # Loop forever
        options: [volatile, noreturn]
```

**What's Needed:**

1. **Inline Assembly Execution**
   ```simple
   fn cpu_id() -> (u32, u32, u32, u32):
       var eax: u32 = 0
       var ebx: u32 = 0
       var ecx: u32 = 0
       var edx: u32 = 0

       asm:
           "cpuid"
           outputs: [eax, ebx, ecx, edx]
           inputs: [eax]
           clobbers: []

       (eax, ebx, ecx, edx)
   ```

2. **Register Constraints**
   ```simple
   fn atomic_add(ptr: ptr<u32>, value: u32) -> u32:
       var result: u32
       asm:
           "lock xadd [{ptr}], {value}"
           ptr = in(reg) ptr,
           value = inout(reg) value => result,
           options: [volatile]
       result
   ```

3. **Memory Barriers**
   ```simple
   fn memory_fence():
       asm:
           "mfence"
           options: [volatile, preserves_flags]
   ```

**Implementation Strategy:**

For **interpreter mode**, inline assembly cannot execute directly. Two options:

**Option A: JIT Required**
```simple
fn eval_inline_asm(asm_expr: HirInlineAsm, ctx: EvalContext) -> Result<Value, BackendError>:
    # Inline assembly requires JIT compilation
    if not ctx.jit_available():
        return Err(BackendError.not_implemented(
            "Inline assembly requires JIT mode - use --jit flag"
        ))

    # Fall back to JIT for this function
    val jit_result = ctx.try_jit_compile_function()
    Ok(jit_result)
```

**Option B: Emulation (Limited)**
```simple
fn eval_inline_asm(asm_expr: HirInlineAsm, ctx: EvalContext) -> Result<Value, BackendError>:
    # Emulate common instructions
    match asm_expr.template:
        case "nop":
            Ok(Value.Unit)
        case "cli":
            # Emulate disable interrupts (no-op in interpreter)
            Ok(Value.Unit)
        case _:
            Err(BackendError.not_implemented(
                "Assembly instruction '{asm_expr.template}' not supported in interpreter"
            ))
```

**Impact:** Enables bare-metal, crypto, SIMD

**Estimated Effort:** 5-7 days (Option A), 2-3 days (Option B limited)

---

### 4. Async/Await ⚠️ (P1 - High)

**Status:** API exists, execution limited

**Blocks:** Async examples, coroutines

**Example:** `examples/async_structure_demo.spl:26-28`
```simple
print "Note: Full execution requires:"
print "  - Function field calls (task.poll_fn())"
print "  - Coroutine suspend/resume"
```

**What's Needed:**

1. **Async Functions**
   ```simple
   async fn fetch_data(url: text) -> Result<text, text>:
       val response = await http_get(url)?
       Ok(response.body)
   ```

2. **Await Expression**
   ```simple
   fn main():
       val data = await fetch_data("https://example.com")
       print data
   ```

3. **Coroutine State Machine**
   ```simple
   # Generated state machine
   struct FetchDataState:
       state: i32
       url: text
       response: Response?

   fn fetch_data_poll(state: FetchDataState, waker: Waker) -> Poll<text>:
       match state.state:
           case 0:
               # First poll: start HTTP request
               state.state = 1
               Poll.Pending
           case 1:
               # Wait for response
               if response_ready():
                   Poll.Ready(response.body)
               else:
                   Poll.Pending
   ```

**Implementation Strategy:**

```simple
# In interpreter backend
impl InterpreterBackendImpl:
    fn eval_expr(expr: HirExpr, ctx: EvalContext) -> Result<Value, BackendError>:
        match expr.kind:
            case Await(future_expr):
                val future = self.eval_expr(future_expr, ctx)?

                # Poll the future until ready
                loop:
                    match self.poll_future(future, ctx):
                        case Poll.Ready(value):
                            return Ok(value)
                        case Poll.Pending:
                            # Yield to executor
                            ctx.yield_execution()

    fn call_async_function(fn_: HirFunction, args: [Value], ctx: EvalContext) -> Result<Value, BackendError>:
        # Create coroutine state
        var coro = Coroutine.new(fn_, args)

        # Poll until complete
        loop:
            match coro.poll(ctx):
                case Poll.Ready(value):
                    return Ok(value)
                case Poll.Pending:
                    ctx.yield_execution()
```

**Impact:** Enables async I/O, concurrency

**Estimated Effort:** 7-10 days (full implementation)

---

### 5. FFI Type Marshaling ⚠️ (P1 - High)

**Status:** Only i64/f64/bool supported

**Blocks:** External library calls, complex FFI

**Current Limitation:** `src/compiler/backend/jit_interpreter.spl:237-249`
```simple
# Convert args to i64 array
# NOTE: This is a simplified implementation
# TODO: Implement full type conversion for all Simple types
var arg_vals: [i64] = []
for arg in args:
    match arg:
        case Int(i):
            arg_vals = arg_vals.push(i)
        case Float(f):
            # TODO: Pass floats as i64 bit pattern
            arg_vals = arg_vals.push(f.to_i64())
        case Bool(b):
            arg_vals = arg_vals.push(if b: 1 else: 0)
        case _:
            # Can't handle complex types via JIT yet
            return nil
```

**What's Needed:**

1. **String Marshaling**
   ```simple
   fn marshal_string(s: text) -> (i64, i64):
       """Convert Simple string to (ptr, len) for FFI."""
       val ptr = rt_string_to_ptr(s)
       val len = s.len()
       (ptr, len)

   fn unmarshal_string(ptr: i64, len: i64) -> text:
       """Convert FFI (ptr, len) to Simple string."""
       rt_ptr_to_string(ptr, len)
   ```

2. **Struct Marshaling**
   ```simple
   struct Point:
       x: f64
       y: f64

   fn marshal_struct(p: Point) -> [i64]:
       """Convert struct to FFI representation."""
       # Layout: [x_low, x_high, y_low, y_high]
       var bytes: [i64] = []
       bytes = bytes.append(marshal_f64(p.x))
       bytes = bytes.append(marshal_f64(p.y))
       bytes
   ```

3. **Array Marshaling**
   ```simple
   fn marshal_array(arr: [i32]) -> (i64, i64):
       """Convert array to (ptr, len) for FFI."""
       val ptr = rt_array_to_ptr(arr)
       val len = arr.len()
       (ptr, len)
   ```

4. **Callback Marshaling**
   ```simple
   fn marshal_callback(fn_: Value) -> i64:
       """Convert Simple function to FFI callback."""
       rt_create_callback(fn_)
   ```

**Implementation:**

```simple
# In JIT interpreter
fn convert_value_to_ffi(value: Value) -> Result<[i64], BackendError>:
    match value:
        case Int(i):
            Ok([i])

        case Float(f):
            Ok(marshal_f64(f))

        case String(s):
            val (ptr, len) = marshal_string(s)
            Ok([ptr, len])

        case Array(elements):
            val (ptr, len) = marshal_array(elements)
            Ok([ptr, len])

        case Struct(ty, fields):
            var bytes: [i64] = []
            for (name, val) in fields:
                bytes = bytes.append(convert_value_to_ffi(val)?)
            Ok(bytes)

        case Function(fn_):
            val callback_ptr = marshal_callback(fn_)
            Ok([callback_ptr])

        case _:
            Err(BackendError.not_implemented("Cannot marshal {value.type_name()}"))

fn convert_ffi_to_value(bytes: [i64], ty: Type) -> Result<Value, BackendError>:
    match ty:
        case Int: Ok(Value.int(bytes[0]))
        case Float: Ok(Value.float(unmarshal_f64(bytes)))
        case String: Ok(Value.string(unmarshal_string(bytes[0], bytes[1])))
        # ... and so on
```

**Impact:** Enables calling any external library from Simple

**Estimated Effort:** 5-7 days

---

### 6. SIMD/GPU ❌ (P2 - Medium)

**Status:** Not implemented in interpreter

**Blocks:** GPU patterns, vectorized math

**Example:** `examples/gpu_patterns/gpu_type_inference_demo.spl`
```simple
fn vector_add_simd(a: [f32; 4], b: [f32; 4]) -> [f32; 4]:
    var result: [f32; 4]
    asm:
        "movups xmm0, [{a}]"
        "movups xmm1, [{b}]"
        "addps xmm0, xmm1"
        "movups [{result}], xmm0"
    result
```

**What's Needed:**

1. **SIMD Types**
   ```simple
   val v1: simd<f32, 4>  # 128-bit SIMD vector
   val v2: simd<i32, 8>  # 256-bit SIMD vector
   ```

2. **SIMD Operations**
   ```simple
   val sum = v1 + v2      # Vector addition
   val prod = v1 * v2     # Vector multiplication
   val dot = v1.dot(v2)   # Dot product
   ```

3. **GPU Kernels** (requires JIT)
   ```simple
   @gpu_kernel
   fn vector_add(a: [f32], b: [f32], out: [f32]):
       val idx = gpu_thread_id()
       out[idx] = a[idx] + b[idx]
   ```

**Implementation:**

SIMD/GPU **requires JIT or AOT compilation** - cannot run in pure interpreter.

**Fallback Strategy:**
```simple
fn eval_simd_op(op: HirSIMDOp, ctx: EvalContext) -> Result<Value, BackendError>:
    if not ctx.jit_available():
        # Fallback to scalar emulation
        return self.emulate_simd_scalar(op, ctx)

    # Use JIT for actual SIMD
    ctx.compile_with_jit()
```

**Impact:** Enables high-performance computing

**Estimated Effort:** 10-14 days (requires significant JIT work)

---

### 7. Parallel Execution ❌ (P2 - Medium)

**Status:** Not implemented

**Blocks:** Parallel file I/O, rayon-style parallelism

**Example:** `examples/file_io/file_staging_parallel.spl`
```simple
fn process_files_parallel(files: [text]):
    files.par_iter().for_each(\f:
        process_file(f)
    )
```

**What's Needed:**

1. **Parallel Iterators**
   ```simple
   val results = data.par_iter()
       .map(\x: compute(x))
       .collect()
   ```

2. **Thread Pool**
   ```simple
   val pool = ThreadPool.new(4)
   pool.spawn(\: heavy_work())
   ```

3. **Parallel Operators**
   ```simple
   val a = [1, 2, 3, 4]
   val b = [5, 6, 7, 8]
   val c = a // b  # Parallel zip
   ```

**Implementation:**

```simple
fn eval_parallel_op(op: HirParallelOp, ctx: EvalContext) -> Result<Value, BackendError>:
    match op:
        case ParMap(iter, fn_):
            # Create thread pool
            val pool = rt_thread_pool_create(cpu_count())

            var results: [Value] = []
            for item in iter:
                # Submit to thread pool
                val future = pool.submit(\: fn_(item))
                results = results.push(future)

            # Wait for all
            val values = results.map(\f: f.wait())
            Ok(Value.Array(values))
```

**Impact:** Enables parallel data processing

**Estimated Effort:** 7-10 days

---

### 8. No-Std/Bare-Metal ❌ (P3 - Low)

**Status:** Not implemented

**Blocks:** Embedded, OS kernels

**Example:** `examples/baremetal/blinky_stm32f4.spl`
```simple
#![no_std]
#![no_main]

fn panic_handler(info: &PanicInfo) -> !:
    loop: pass
```

**What's Needed:**

1. **No-Std Mode**
   ```simple
   #![no_std]  # Disable standard library
   ```

2. **Custom Panic Handler**
   ```simple
   fn panic_handler(info: PanicInfo):
       # Custom panic implementation
       halt()
   ```

3. **Custom Allocator**
   ```simple
   @global_allocator
   static ALLOCATOR: BumpAllocator = BumpAllocator.new()
   ```

**Implementation:**

Bare-metal **requires AOT compilation** - interpreter cannot support no-std mode.

**Impact:** Enables embedded systems programming

**Estimated Effort:** N/A (requires compiler, not interpreter)

---

## Implementation Priorities

### Phase 1: Enable JIT for All Code (P0)

**Goal:** Make interpreter capable of running complex code via JIT

**Features:**
1. ✅ MIR Serialization
2. ✅ FFI Type Marshaling
3. ✅ Unsafe Code Support

**Effort:** 10-15 days
**Impact:** 90% of examples work

### Phase 2: Async and Assembly (P1)

**Goal:** Support async patterns and low-level code

**Features:**
1. ✅ Async/Await Execution
2. ✅ Inline Assembly (JIT mode)

**Effort:** 12-17 days
**Impact:** 95% of examples work

### Phase 3: Performance (P2)

**Goal:** Enable high-performance code

**Features:**
1. ✅ SIMD/GPU Support
2. ✅ Parallel Execution

**Effort:** 17-24 days
**Impact:** 98% of examples work

### Phase 4: Bare-Metal (P3)

**Goal:** Embedded systems support

**Features:**
1. ✅ No-Std Mode

**Effort:** N/A (requires AOT compiler)
**Impact:** 100% of examples work

## Current Workarounds

### For Users Right Now

**1. JIT Mode for Complex Code**
```bash
# Use JIT mode instead of pure interpretation
simple run --jit myapp.spl
```

**2. Compiler Mode for Bare-Metal**
```bash
# Use AOT compilation for bare-metal
simple build --bare-metal hello_x86.spl
```

**3. Skip Unsupported Features**
```simple
#[cfg(not(interpret))]
fn use_simd():
    # SIMD code here
    ...

#[cfg(interpret)]
fn use_simd():
    # Scalar fallback
    ...
```

## Summary Table

| Feature | Examples Blocked | Interpreter Support | JIT Support | AOT Support | Priority |
|---------|------------------|---------------------|-------------|-------------|----------|
| Standard Simple | All | ✅ Yes | ✅ Yes | ✅ Yes | - |
| MIR Serialization | JIT examples | ⚠️ Framework only | ⚠️ Needs impl | ✅ Yes | P0 |
| Unsafe Code | Bare-metal | ❌ No | ⚠️ Needs impl | ✅ Yes | P0 |
| FFI Marshaling | External libs | ⚠️ Partial | ⚠️ Partial | ✅ Yes | P1 |
| Inline Assembly | Low-level | ❌ No | ⚠️ Needs impl | ✅ Yes | P1 |
| Async/Await | Async code | ⚠️ Partial | ⚠️ Partial | ✅ Yes | P1 |
| SIMD/GPU | Performance | ❌ No | ⚠️ Needs impl | ✅ Yes | P2 |
| Parallel | Data processing | ❌ No | ⚠️ Needs impl | ✅ Yes | P2 |
| No-Std | Embedded | ❌ No | ❌ No | ✅ Yes | P3 |

**Legend:**
- ✅ Fully supported
- ⚠️ Partially supported / needs work
- ❌ Not supported

## Conclusion

**To run ALL tests/examples in interpreter mode:**

**Phase 1 (Critical):** 10-15 days
1. MIR Serialization
2. FFI Type Marshaling
3. Unsafe Code Support

**Phase 2 (High):** +12-17 days (27-32 total)
4. Async/Await Execution
5. Inline Assembly

**Phase 3 (Medium):** +17-24 days (44-56 total)
6. SIMD/GPU Support
7. Parallel Execution

**Phase 4 (Low):** Requires AOT compiler
8. No-Std/Bare-Metal

**Realistic Timeline:** ~6-8 weeks for interpreter to support 98% of examples

**Recommended Approach:** Focus on Phase 1 (P0) first, as it unblocks the most examples with JIT support.

---

**Status:** Analysis Complete
**Total Features:** 8
**Critical Path:** MIR Serialization → Type Marshaling → Unsafe Code
**Estimated Total Effort:** 44-56 days for 98% coverage
