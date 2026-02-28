# SFFI Dynamic Loading: Interpreter JIT Mode & .so/.dll Extension

**Date:** 2026-02-21
**Status:** Research Complete, Implementation Paths Identified
**Context:** PyTorch SFFI integration revealed interpreter whitelist limitations

---

## 1. Executive Summary

The `simple` interpreter (Rust binary at `bin/release/simple`) has a **fixed whitelist of 129 extern functions** compiled into it. Unknown `extern fn` calls produce:

```
error: semantic: unknown extern function: rt_torch_available
```

`spl_dlopen`, `spl_dlsym`, and `spl_wffi_call_i64` are **also absent** from this whitelist, meaning the existing WFFI module (`src/compiler/10.frontend/core/wffi/mod.spl`) cannot be used from interpreter mode.

**The good news:** The C-backend compiled mode **already works** — runtime.h has full WFFI/dlopen support, and `build/libspl_torch.so` (161 KB) is proven to work via direct C++ test showing GPU activity on nvidia-smi.

---

## 2. Current Architecture

### 2.1 The Three Execution Modes

```
bin/simple <file.spl>
    └─ bin/release/simple (self-hosted binary, 33 MB, fully self-sufficient)
           ├─ Interpreter mode (default, in-process via interpret_file())
           │    └─ match extern_name in whitelist of 129 names
           │         _ => error("unknown extern function: {name}")
           ├─ Compilation mode (in-process, no subprocess delegation)
           │    └─ aot_c_file(), compile_native(), aot_vhdl_file()
           │         (all compilation happens in-process)
           └─ Cranelift JIT (native, not present in current build)
                └─ rt_exec_manager_create("cranelift") → not working

bin/simple compile --backend=c && cmake && ninja
    └─ C-compiled binary
           └─ Calls spl_dlopen / spl_wffi_call_i64 from runtime.c (WORKS)
```

**Note (2026-02-28):** The "soft exec_manager" subprocess pattern has been eliminated. The self-hosted binary no longer shells out to `bin/simple` or `bin/release/simple` for any compilation, interpretation, or test running. All operations are in-process.

### 2.2 JIT Mode

**Note (2026-02-28):** The "soft exec_manager" subprocess fallback has been eliminated. The self-hosted binary now handles all file execution in-process via `interpret_file()`. The old pattern of shelling out to `bin/simple -c "{code}"` is no longer used.

**Real Cranelift JIT** (`src/compiler/95.interp/execution/mod.spl`):
- `rt_exec_manager_create("cranelift")` — not implemented in current binary build
- Would require `cranelift_jit` feature to be compiled in

### 2.3 Why the Whitelist Exists

The Rust binary (`compiler/src/interpreter_extern/mod.rs`) has a match statement:
```rust
pub(crate) fn call_extern_function(name: &str, args: Vec<Value>) -> Result<Value, CompileError> {
    match name {
        "rt_print" => io::print::print(&args),
        // ... 128 more ...
        _ => Err(CompileError::Semantic(format!("unknown extern function: {}", name))),
    }
}
```

This was refactored (phase11) into 17 modules but the whitelist is still compiled in.

### 2.4 WFFI: Exists but Unavailable in Interpreter

`src/compiler/10.frontend/core/wffi/mod.spl` has the right API:
```simple
extern fn spl_dlopen(path: text) -> i64
extern fn spl_dlsym(handle: i64, name: text) -> i64
extern fn spl_wffi_call_i64(fptr: i64, args: [i64], nargs: i64) -> i64
```

**Status by mode:**
| Mode | spl_dlopen | spl_dlsym | spl_wffi_call_i64 | rt_torch_* |
|------|-----------|-----------|-------------------|------------|
| Interpreter (Rust binary) | ❌ whitelist | ❌ whitelist | ❌ whitelist | ❌ whitelist |
| C-compiled binary | ✅ runtime.h | ✅ runtime.h | ✅ runtime.c | ✅ if linked |
| soft exec_manager | ❌ same whitelist | ❌ | ❌ | ❌ |

### 2.5 What IS Available in Interpreter

The 129 whitelisted functions include:
- I/O: `rt_print_str`, `rt_println_str`, `rt_eprint_str`, `rt_eprintln_str`
- File: `rt_file_read_text`, `rt_file_write_text`, `rt_file_exists`, `rt_file_find`, `rt_dir_glob`
- Env: `rt_env_get`, `rt_env_set`, `rt_exit`
- Process: `rt_process_run`, `rt_execute_native` (runs a binary, returns (stdout, stderr, exit_code))
- Collections: `rt_hashmap_*`, `rt_btreemap_*`, `rt_hashset_*`
- Atomics: `rt_atomic_int_*`, `rt_atomic_bool_*`
- Actors: `rt_actor_spawn`, `rt_actor_send`, `rt_actor_recv`
- Time: `rt_time_now_monotonic_ms`
- Sandbox: `rt_sandbox_*`

**Notably missing:** `spl_dlopen`, `spl_dlsym`, `spl_dlclose`, `spl_wffi_call_i64`

---

## 3. Implementation Paths for Dynamic .so/.dll Loading

### Path 1: Add WFFI to the Simple Interpreter Source (Recommended)

**Where:** `src/compiler/95.interp/mir_interpreter.spl` — the Simple-language re-implementation of the interpreter. When the bootstrap cycle produces a new binary, this would replace the Rust implementation.

**What to add:** A dynamic library registry in the interpreter's exec context.

```simple
# In src/compiler/95.interp/interpreter/extern_dispatch.spl (NEW)

class ExternDispatcher:
    """Dispatches extern fn calls: first checks whitelist, then dynamic libs."""
    dynamic_libs: {text: i64}     # prefix -> lib handle
    func_cache: {text: i64}       # func_name -> fptr

    fn call(name: text, args: [i64]) -> i64:
        # 1. Check built-in whitelist (delegate to existing handlers)
        val builtin = self.call_builtin(name, args)
        if builtin.?:
            return builtin.unwrap()
        # 2. Try to load dynamic lib by convention
        val lib_path = self.resolve_lib_for(name)
        if lib_path.?:
            val fptr = self.load_and_get(lib_path.unwrap(), name)
            if fptr != 0:
                return self.call_fptr(fptr, args)
        0

    fn resolve_lib_for(name: text) -> text?:
        # Convention: rt_torch_* -> libspl_torch.so
        # Convention: rt_audio_* -> libspl_audio.so
        if name.starts_with("rt_torch_"):
            Some(rt_env_get("SIMPLE_TORCH_LIB") ?? "build/libspl_torch.so")
        else:
            nil
```

**Benefit:** Shared logic across interpreter and compiler — ExternDispatcher can be used by both.

### Path 2: Expose spl_dlopen in the Rust Interpreter (Requires Binary Update)

Add to `interpreter_extern/mod.rs`:
```rust
"spl_dlopen" => native_ffi::spl_dlopen(&evaluated),
"spl_dlsym" => native_ffi::spl_dlsym(&evaluated),
"spl_dlclose" => native_ffi::spl_dlclose(&evaluated),
"spl_wffi_call_i64" => native_ffi::spl_wffi_call_i64(&evaluated),
```

And implement in `native_ffi.rs`:
```rust
pub fn spl_dlopen(args: &[Value]) -> Result<Value, CompileError> {
    let path = arg_extract::as_str(args, 0, "spl_dlopen")?;
    unsafe {
        let cstr = CString::new(path.as_str()).map_err(|_| CompileError::Runtime("bad path".into()))?;
        let handle = libc::dlopen(cstr.as_ptr(), libc::RTLD_NOW);
        Ok(Value::Int(handle as i64))
    }
}
```

**Benefit:** Works immediately in the current binary once rebuilt. Minimal change.

### Path 3: Process-Bridge Approach (Works Today, No Binary Change)

Use `rt_execute_native` (available in interpreter) to run a bridge process:

```simple
# torch_bridge.spl — compiled to native binary, loads libspl_torch.so
extern fn spl_dlopen(path: text) -> i64
extern fn spl_dlsym(handle: i64, name: text) -> i64
extern fn spl_wffi_call_i64(fptr: i64, args: [i64], nargs: i64) -> i64

fn torch_available() -> bool:
    val lib = spl_dlopen("build/libspl_torch.so")
    val f = spl_dlsym(lib, "rt_torch_available")
    spl_wffi_call_i64(f, [], 0) == 1

val a = torch_available()
print "{a}"   # stdout: true or false
```

Then from interpreter:
```simple
extern fn rt_execute_native(binary: text, args: [text], timeout_ms: i64) -> (text, text, i64)

fn torch_available_interp() -> bool:
    val (out, _, _) = rt_execute_native("bin/torch_bridge", [], 5000)
    out.trim() == "true"
```

**Downside:** Subprocess overhead per call (~50-100ms). Fine for availability check, bad for tensor ops.

---

## 4. Recommended Architecture: Shared ExternDispatcher

### 4.1 Design Principles

- **Single source of truth:** `src/lib/ffi/extern_dispatch.spl` contains dispatch logic
- **Compiled mode:** Uses WFFI directly via `spl_dlopen`/`spl_wffi_call_i64`
- **Interpreter mode:** Delegates to `rt_execute_native` helper binary (until binary is updated)
- **Convention over config:** `rt_LIBNAME_*` maps to `libspl_LIBNAME.so`

### 4.2 File Structure

```
src/lib/ffi/
├── mod.spl                    # Existing FFI declarations
├── dynamic.spl                # NEW: Dynamic library loader
│   ├── class DynLib           # Wrapper around dlopen handle
│   ├── class DynLoader        # Registry of loaded libraries
│   └── fn load_for_prefix()   # Convention-based loading
└── torch_bridge.spl           # NEW: Compiled helper binary

src/compiler/95.interp/interpreter/
└── extern_registry.spl        # NEW: Interpreter extern dispatch with dynamic loading

src/compiler/99.loader/loader/
└── extern_loader.spl          # NEW: Shared extern loading logic for compiled mode
```

### 4.3 Convention-Based Loading

```simple
# SFFI naming convention: rt_{lib}_{function}
# Library file: $SIMPLE_SFFI_PATH/libspl_{lib}.so (or .dll on Windows)

fn sffi_lib_path(prefix: text) -> text:
    val base = rt_env_get("SIMPLE_SFFI_PATH") ?? "build"
    val ext = if rt_platform() == "windows": ".dll" else: ".so"
    "{base}/libspl_{prefix}{ext}"

fn sffi_call(func_name: text, args: [i64]) -> i64:
    # Parse prefix: "rt_torch_available" -> "torch"
    val parts = func_name.split("_")
    if parts.len() < 3: return 0  # malformed
    val prefix = parts[1]  # "torch", "audio", etc.
    val lib_path = sffi_lib_path(prefix)
    DynLoader.instance().call(lib_path, func_name, args)
```

### 4.4 Sharing Logic: Compiler vs Interpreter

The key insight: both the C-compiled binary and the interpreter need the same dispatch logic. The only difference is HOW `spl_dlopen` is called:

| Layer | How dlopen works |
|-------|-----------------|
| C-compiled binary | Direct C call to `dlopen()` via `spl_dlopen` in runtime.h |
| Interpreter (future) | `ExternDispatcher.call_builtin("spl_dlopen", [path])` |
| Interpreter (today) | Subprocess via `rt_execute_native` bridge binary |

The Simple-language code in `DynLoader` is **identical** for both modes — only the underlying `spl_dlopen` extern differs.

---

## 5. Minimal Implementation Plan

### Phase A: Compiler/Compiled Mode (Works Today)

1. **Create `src/lib/ffi/dynamic.spl`:**
   - `DynLib` class wrapping `spl_dlopen`/`spl_dlsym`/`spl_dlclose`
   - `DynLoader` singleton with library cache
   - `fn call_rt(func_name, args)` with convention-based loading

2. **Wire `src/lib/gc_async_mut/torch/ffi.spl`:**
   - Replace each `extern fn rt_torch_*` with a WFFI call through `DynLoader`
   - On first call: `DynLoader.load("build/libspl_torch.so")`

3. **Test via C-backend compilation:**
   ```bash
   bin/simple compile --backend=c -o build/torch_test/ test/unit/lib/torch_spec.spl
   cmake -B build/torch_test_cmake && ninja -C build/torch_test_cmake
   ./build/torch_test_cmake/torch_test
   ```

### Phase B: Interpreter Mode (Requires Binary Change OR Subprocess Bridge)

**Option B1:** Add `spl_dlopen`/`spl_dlsym`/`spl_wffi_call_i64` to interpreter binary.
- Modify `interpreter_extern/native_ffi.rs` in Rust source (if available)
- Or add to the Simple-source interpreter `src/compiler/95.interp/`

**Option B2 (bridge):** Compile a tiny `torch_bridge` binary that:
- Is invoked via `rt_execute_native`
- Takes torch function name + args on stdin (JSON/SDN)
- Loads `libspl_torch.so`, calls the function, prints result on stdout
- Returns i64 result

### Phase C: Shared Logic Refactor

Move the extern dispatch to `src/compiler/95.interp/interpreter/extern_registry.spl`:
```simple
class ExternRegistry:
    """Shared extern dispatch for both interpreter and compiled modes."""
    builtins: {text: fn([i64]) -> i64}
    dynamic: DynLoader

    fn call(name: text, args: [i64]) -> i64:
        val b = self.builtins.get(name)
        if b.?:
            b.unwrap()(args)
        else:
            self.dynamic.call_rt(name, args)
```

Used by:
- `MirInterpreter` (interpreter mode)
- `CBackend` extern call emission (compiled mode)
- `ModuleLoader` (loader mode)

---

## 6. Quick Win: What Works Today

The C++ bridge (`build/libspl_torch.so`) is proven to work. The direct test showed:
- `rt_torch_available()` → `yes`
- GPU tensor matmul: 2000×2000 × 2000×2000 = result on CUDA ✅
- nvidia-smi: 342 MiB on GPU 0, process in list, power 11W → 65W ✅

**To use today (compiled mode only):**
```bash
# Build the .so (already done)
bash scripts/build/build-torch-ffi.sh  # → build/libspl_torch.so

# Compile torch test with C backend
bin/simple compile --backend=c -o build/torch_test/ /tmp/torch_hello.spl
# Add -L build -lspl_torch to CMakeLists.txt
cmake -B build/torch_cmake && ninja -C build/torch_cmake
LD_LIBRARY_PATH=build ./build/torch_cmake/simple
```

**Interpreter mode:** Not possible without one of the Phase B options above.

---

## 7. Conclusion

| What | Current Status | Fix |
|------|---------------|-----|
| `rt_torch_*` in interpreter | ❌ Not in whitelist | Add spl_dlopen to binary OR add ExternRegistry to Simple interpreter source |
| WFFI (`spl_dlopen`) in interpreter | ❌ Not in whitelist | Same as above |
| `rt_torch_*` in C-compiled binary | ✅ Works via runtime.h | Use WFFI + `build/libspl_torch.so` |
| GPU activity proven | ✅ Via direct C++ test | `build/libspl_torch.so` already built |
| Subprocess delegation | ✅ Eliminated (2026-02-28) | All compilation/interpretation now in-process |
| Native Cranelift JIT | ❌ Not in binary build | Would require feature-enabled rebuild |

**Recommended next step:** Implement `src/lib/ffi/dynamic.spl` and update `torch/ffi.spl` to use WFFI calls, enabling torch FFI in C-compiled mode. For interpreter support, add `spl_dlopen`/`spl_dlsym`/`spl_wffi_call_i64` to `src/compiler/95.interp/` so they're available in the next bootstrap cycle.
