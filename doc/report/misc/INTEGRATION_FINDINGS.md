# PyTorch SFFI Integration - Runtime Loading Analysis

## Finding: External FFI Libraries Not Auto-Loaded

### Test Results

**Built-in extern fn (works ✅):**
```simple
extern fn rt_env_get(key: text) -> text
val home = rt_env_get("HOME")  # Returns: /home/ormastes
```

**External extern fn (fails ❌):**
```simple
extern fn rt_torch_available() -> bool
val available = rt_torch_available()  # Error: unknown extern function
```

### Root Cause

The Simple runtime has two types of `extern fn`:

1. **Built-in Functions** (in runtime binary)
   - Examples: `rt_env_get`, `rt_file_read`, `rt_process_run`
   - Location: Compiled into `bin/bootstrap/simple`
   - Work immediately with `extern fn` declaration

2. **External Library Functions** (in .so files)
   - Examples: `rt_torch_available`, `rt_opencv_imread`
   - Location: External `.so` files like `libsimple_torch.so`
   - **NOT automatically loaded by runtime**

### The Missing Link

**Problem:** Runtime doesn't know to load `libsimple_torch.so` when it sees `extern fn rt_torch_available()`

**Possible Solutions:**

**Option A: Compile-Time Linking (Most Likely)**
Link FFI libraries into the runtime when building it:
```bash
# Add to runtime build configuration
LINK_LIBRARIES="libsimple_torch.so"
# Rebuild runtime with FFI libraries linked
```

**Option B: LD_PRELOAD (Workaround)**
```bash
LD_PRELOAD=.build/rust/ffi_torch/target/release/libsimple_torch.so \
  bin/simple test_torch.spl
```

**Option C: Dynamic Loading (Needs Implementation)**
Runtime would need code like:
```simple
# When encountering unknown extern fn rt_torch_*:
# 1. Extract library name: "torch" from "rt_torch_*"
# 2. Look for .build/rust/ffi_torch/target/release/libsimple_torch.so
# 3. dlopen() the library
# 4. dlsym() to resolve rt_torch_available
# 5. Cache for future calls
```

**Option D: Explicit Load (Manual)**
```simple
# User code would need:
use ffi.{load_library}
val torch_lib = load_library(".build/rust/ffi_torch/target/release/libsimple_torch.so")
# Then extern fn would work...maybe?
```

### Next Steps

1. **Investigate runtime build system** - How are FFI libraries linked?
2. **Test LD_PRELOAD** - Quick verification that library functions work
3. **Check for FFI configuration** - Is there a config file for FFI libraries?
4. **Consider runtime modification** - Add auto-loading for `libsimple_*.so` files

### Test LD_PRELOAD

Let me try this immediately:
