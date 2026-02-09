# PyTorch Examples Unblock Plan

**Date:** 2026-02-09
**Context:** 5 PyTorch examples implemented (976 lines), blocked by 2 runtime issues

---

## Current Status

### ✅ What Works

- **Examples:** 5 complete cuda:1 examples (583 LOC)
- **Documentation:** Comprehensive README (393 LOC)
- **Configuration:** dl.config.sdn with cuda:1 setup
- **Code Quality:** No syntax errors, consistent style
- **Imports:** Correct module structure

### ⚠️ Blockers

**BLOCKER 1:** Runtime parser fails on `GPU` enum variant in config.spl
**BLOCKER 2:** Runtime semantic analyzer rejects unknown extern functions

---

## Three-Phase Unblock Plan

### Phase 1: Fix Parser Issue (5-10 minutes) 🔧

**Goal:** Make config.spl parseable by runtime

**Problem:**
```simple
enum Device:
    CPU
    GPU             # ← Parser error: "expected identifier, found Gpu"
    CUDA(id: i32)
```

**Solution: Remove GPU variant (cleaner approach)**

#### Step 1.1: Edit config.spl
```simple
# File: src/std/src/dl/config.spl
# Line 62-66

# BEFORE:
enum Device:
    CPU
    GPU             # Default GPU (typically CUDA:0)
    CUDA(id: i32)   # Specific CUDA device

# AFTER:
enum Device:
    """Device for tensor computation."""
    CPU                # CPU computation
    CUDA(id: i32)      # CUDA device (0=1st GPU, 1=2nd GPU, etc.)
```

#### Step 1.2: Update Device impl methods
```simple
# File: src/std/src/dl/config.spl
# Line 74-77

# BEFORE:
fn is_gpu() -> bool:
    match self:
        case GPU | CUDA(_): true
        case CPU: false

# AFTER:
fn is_gpu() -> bool:
    match self:
        case CUDA(_): true
        case CPU: false
```

```simple
# File: src/std/src/dl/config.spl
# Line 79-84

# BEFORE:
fn cuda_id() -> i32?:
    match self:
        case CUDA(id): Some(id)
        case GPU: Some(0)
        case CPU: nil

# AFTER:
fn cuda_id() -> i32?:
    """Return the CUDA device ID, or None if not a CUDA device."""
    match self:
        case CUDA(id): Some(id)
        case CPU: nil
```

```simple
# File: src/std/src/dl/config.spl
# Line 86-90

# BEFORE:
fn to_string() -> text:
    match self:
        case CPU: "cpu"
        case GPU: "gpu"
        case CUDA(id): "cuda:{id}"

# AFTER:
fn to_string() -> text:
    match self:
        case CPU: "cpu"
        case CUDA(id): "cuda:{id}"
```

#### Step 1.3: Update config_loader.spl
```simple
# File: src/std/src/dl/config_loader.spl
# Find device parsing logic (around line 100-120)

# BEFORE:
fn parse_device(device_str: text) -> Device:
    if device_str == "cpu":
        Device.CPU
    else if device_str == "gpu":
        Device.GPU
    else if device_str.starts_with("cuda"):
        # Parse cuda:N
        val parts = device_str.split(":")
        if parts.len() == 2:
            val id = int(parts[1])
            Device.CUDA(id)
        else:
            Device.CUDA(0)
    else:
        Device.CPU  # Default

# AFTER:
fn parse_device(device_str: text) -> Device:
    """Parse device string into Device enum.

    Examples:
      "cpu" → Device.CPU
      "cuda:0" → Device.CUDA(0)
      "cuda:1" → Device.CUDA(1)
      "gpu" → Device.CUDA(0) (default GPU = 1st GPU)
    """
    if device_str == "cpu":
        Device.CPU
    else if device_str == "gpu":
        Device.CUDA(0)  # Default GPU = 1st GPU
    else if device_str.starts_with("cuda"):
        # Parse cuda:N
        val parts = device_str.split(":")
        if parts.len() == 2:
            val id = int(parts[1])
            Device.CUDA(id)
        else:
            Device.CUDA(0)  # Default to 1st GPU if no ID specified
    else:
        Device.CPU  # Default to CPU for unknown strings
```

#### Step 1.4: Update documentation
```bash
# Files to update:
# - doc/guide/gpu_configuration.md (change GPU → CUDA(0) in examples)
# - examples/torch/README.md (update Device enum docs)
```

**Changes:**
- Remove all mentions of `Device.GPU`
- Replace with `Device.CUDA(0)` or just document `CPU` and `CUDA(id)`

#### Step 1.5: Verify fix
```bash
# Test that config.spl parses:
bin/bootstrap/simple test_gpu_config.spl 2>&1 | grep -i "parse"

# Should NOT see: "Failed to parse module...Gpu"
# Should see: "error: semantic: function `torch_available` not found"
#   (This means parser worked, semantic analyzer is next blocker)
```

**Success Criteria:**
- ✅ config.spl parses without errors
- ✅ Examples load config successfully
- ✅ Fail at semantic analysis stage (BLOCKER 2) instead of parse stage

**Time Estimate:** 5-10 minutes

---

### Phase 2: Test Examples Load Correctly (5 minutes) ✅

**Goal:** Verify examples can load and fail gracefully at FFI call

#### Step 2.1: Run each example
```bash
bin/bootstrap/simple examples/torch/basics/01_tensor_creation.spl 2>&1 | tee test_01.log
bin/bootstrap/simple examples/torch/basics/02_tensor_operations.spl 2>&1 | tee test_02.log
bin/bootstrap/simple examples/torch/basics/03_device_selection.spl 2>&1 | tee test_03.log
bin/bootstrap/simple examples/torch/training/xor_pytorch.spl 2>&1 | tee test_04.log
bin/bootstrap/simple examples/torch/training/mnist_classifier.spl 2>&1 | tee test_05.log
```

#### Step 2.2: Expected output pattern
```
=== PyTorch Tensor Creation (CUDA:1 - 2nd GPU) ===

Backend Check:
error: semantic: function `torch_available` not found
```

**Good Signs:**
- ✅ Header printed (module loaded)
- ✅ Config loaded (no parse errors)
- ✅ Clear error message about missing function

**Bad Signs:**
- ❌ Parse error on config.spl → Phase 1 fix incomplete
- ❌ Import error → Check module paths
- ❌ Crash or unclear error → Unexpected issue

#### Step 2.3: Document test results
```bash
# Create test results file
cat > doc/test_results_2026-02-09.txt <<EOF
PyTorch Examples Test Results (2026-02-09)

Phase 1 Complete: Parser fix applied
Phase 2 Testing: Load and fail gracefully

Test Results:
1. 01_tensor_creation.spl: [PASS/FAIL] - [error message]
2. 02_tensor_operations.spl: [PASS/FAIL] - [error message]
3. 03_device_selection.spl: [PASS/FAIL] - [error message]
4. xor_pytorch.spl: [PASS/FAIL] - [error message]
5. mnist_classifier.spl: [PASS/FAIL] - [error message]

Summary:
- Parser errors: [count]
- Semantic errors (expected): [count]
- Unexpected errors: [count]

Next: Phase 3 (Runtime FFI loading) or STOP if not proceeding
EOF
```

**Success Criteria:**
- ✅ All examples load without parse errors
- ✅ All examples fail at semantic analysis (torch_available not found)
- ✅ Error messages are clear and helpful

**Time Estimate:** 5 minutes

---

### Phase 3: Runtime FFI Loading (2-3 hours) ⏸️ OPTIONAL

**⚠️ User Decision Required:** This phase requires modifying runtime internals.

**Goal:** Allow runtime to accept unknown extern functions and resolve at execution time

#### Current Behavior:
```
extern fn rt_torch_available() -> bool
  ↓
Semantic analyzer: "function rt_torch_available not found"
  ↓
STOP (before execution)
```

#### Desired Behavior:
```
extern fn rt_torch_available() -> bool
  ↓
Semantic analyzer: Accept (defer to runtime)
  ↓
Runtime linker: Look up symbol in loaded libraries
  ↓
If found: Execute
If not found: "Symbol rt_torch_available not found in loaded libraries"
```

#### Step 3.1: Analyze current semantic analyzer

**Files to investigate:**
```
src/app/interpreter.*/semantic_analyzer.spl (or Rust runtime equivalent)
src/app/interpreter.*/module_loader.spl
```

**Questions:**
1. Where does semantic analyzer check extern fn existence?
2. What's the list of "known" extern functions?
3. How can we defer checking to runtime?

#### Step 3.2: Modify semantic analyzer

**Approach A: Accept all extern fn**
```simple
# In semantic analyzer:
# BEFORE:
fn check_extern_fn(name: text):
    if not is_builtin_extern(name):
        error("unknown extern function: {name}")

# AFTER:
fn check_extern_fn(name: text):
    # Accept all extern fn declarations
    # Resolution happens at runtime/link time
    register_extern_fn(name, signature)
```

**Approach B: Load extern registry from FFI libraries**
```simple
# In module loader:
# 1. When loading module with extern fn:
#    - Check if library defines these functions (.so symbol table)
#    - Add to runtime symbol table
# 2. When calling extern fn:
#    - Look up in runtime symbol table
#    - Call if found, error if not
```

#### Step 3.3: Implement runtime symbol resolution

**Pseudo-code:**
```simple
class RuntimeSymbolTable:
    symbols: {text: FnPtr}  # name → function pointer

    fn register_library(lib_path: text):
        val lib = dlopen(lib_path)
        for symbol in lib.symbols():
            if symbol.starts_with("rt_"):
                self.symbols[symbol] = lib.get_symbol(symbol)

    fn resolve(name: text) -> FnPtr?:
        self.symbols.get(name)

# In runtime:
var symbol_table = RuntimeSymbolTable()

# Auto-load FFI libraries:
symbol_table.register_library("libsimple_torch_ffi.so")
symbol_table.register_library("libsimple_regex_ffi.so")
# ... etc

# When calling extern fn:
fn call_extern_fn(name: text, args: [Value]) -> Value:
    val fn_ptr = symbol_table.resolve(name)
    if fn_ptr.is_none():
        error("Symbol {name} not found in loaded libraries")
    fn_ptr.call(args)
```

#### Step 3.4: Update FFI library loading

**Auto-load strategy:**
```simple
# In runtime initialization:
fn load_ffi_libraries():
    val lib_dirs = [
        "/usr/local/lib",
        "~/.simple/lib",
        "./build/lib"
    ]

    for dir in lib_dirs:
        for file in glob("{dir}/libsimple_*_ffi.so"):
            try:
                symbol_table.register_library(file)
                print "Loaded FFI: {file}"
            catch:
                # Silent fail - library may not be available
                pass
```

**Manual load strategy:**
```simple
# In user code:
use std.ffi.{load_ffi_library}

fn main():
    load_ffi_library("torch")  # Loads libsimple_torch_ffi.so
    # Now rt_torch_* functions are available
```

#### Step 3.5: Test with PyTorch FFI

```bash
# 1. Build PyTorch FFI library
cd .build/rust/ffi_torch
export LIBTORCH_PATH=/opt/libtorch
cargo build --release

# 2. Install to system
sudo cp target/release/libsimple_torch_ffi.so /usr/local/lib/
sudo ldconfig

# 3. Run examples
bin/bootstrap/simple examples/torch/basics/01_tensor_creation.spl

# Expected:
# - Semantic analysis: PASS (accepts extern fn)
# - Runtime loading: PASS (finds rt_torch_available)
# - Function call: PASS (executes)
# - Output: "torch_available() = true"
```

**Success Criteria:**
- ✅ Semantic analyzer accepts unknown extern fn
- ✅ Runtime loads FFI libraries automatically or on-demand
- ✅ Examples execute successfully with PyTorch
- ✅ Clear error if library not installed

**Time Estimate:** 2-3 hours

**⚠️ DECISION POINT:** Proceed with Phase 3 or stop here?

---

## Decision Tree

```
START
  ↓
Do you want to fix parser issue (5 min)?
  ├─ YES → Phase 1: Fix GPU enum variant
  │         ↓
  │       Test examples load correctly?
  │         ├─ YES → Phase 2: Document success
  │         │         ↓
  │         │       Do you want runtime FFI loading (2-3 hrs)?
  │         │         ├─ YES → Phase 3: Modify runtime
  │         │         │         ↓
  │         │         │       Test with PyTorch
  │         │         │         ↓
  │         │         │       COMPLETE ✅
  │         │         │
  │         │         └─ NO → STOP (examples ready, waiting for FFI)
  │         │
  │         └─ NO → Debug Phase 1 fix
  │
  └─ NO → STOP (examples implemented, not tested)
```

---

## Recommendations

### Immediate Next Steps (5-10 minutes):

1. **Fix parser issue** (Phase 1)
   - Low risk, quick fix
   - Unblocks examples from loading
   - No runtime modification needed

2. **Test examples** (Phase 2)
   - Verify fix works
   - Document current state
   - Clear stopping point

### Future Work (Optional, 2-3 hours):

3. **Runtime FFI loading** (Phase 3)
   - Requires runtime modification
   - Benefits all external FFI libraries
   - One-time infrastructure work

### Alternative Path (If not modifying runtime):

**Document "Ready to Run" Status:**
- Examples are complete and correct
- Waiting for runtime FFI loading feature
- Can be tested once feature is implemented
- No further work needed on examples themselves

---

## Summary

**What's Implemented:** ✅
- 5 complete PyTorch examples (583 LOC)
- Comprehensive documentation (393 LOC)
- cuda:1 configuration throughout
- Clear error handling

**What's Blocking:** ⚠️
- Parser issue with GPU enum (5-min fix)
- Runtime doesn't support external FFI (2-3 hour fix)

**Recommended Action:**
1. Fix parser issue (Phase 1) → 5-10 minutes
2. Test examples load (Phase 2) → 5 minutes
3. Decide on Phase 3 based on priorities

**Total Time to "Examples Ready":** 10-15 minutes
**Total Time to "Examples Working":** 2-3 hours (if doing runtime work)
