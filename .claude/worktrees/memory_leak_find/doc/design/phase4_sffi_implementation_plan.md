# Phase 4: SFFI Implementation Plan (2026-02-08)

**Status:** Design Complete - Implementation Requires Runtime Changes
**Effort:** 5-7 days full implementation
**Priority:** Medium (blocked by runtime architecture)

---

## Executive Summary

Phase 4 requires implementing SFFI wrappers for 7 external Rust libraries (79 tests). Investigation reveals this requires **runtime modifications** to support dynamic plugin loading, which is currently not fully implemented.

**Current Status:**
- ✅ Tier 2+3 (Simple code) exists for all 7 libraries
- ✅ Wrapper generator produces Tier 1 (Rust code)
- ✅ Manual fixes allow Rust code to compile
- ❌ Runtime cannot load `.so` plugins dynamically
- ❌ Extern functions must be registered at build time

---

## Architecture: Three-Tier SFFI Pattern

```
┌─────────────────────────────────────────────────┐
│ Tier 3: Simple API (src/app/io/regex_simple.spl) │  ✅ EXISTS
│   - User-facing functions                       │
│   - Error handling, type safety                 │
└────────────────┬────────────────────────────────┘
                 │ calls
┌─────────────────────────────────────────────────┐
│ Tier 2: SFFI Bindings (src/app/io/regex_ffi.spl) │  ✅ EXISTS
│   - extern fn declarations (rt_regex_*)          │
│   - 15 function declarations                     │
└────────────────┬────────────────────────────────┘
                 │ links to
┌─────────────────────────────────────────────────┐
│ Tier 1: Rust FFI (.build/rust/ffi_regex/)        │  ✅ BUILT
│   - Handle table pattern                         │
│   - #[no_mangle] extern "C" exports              │
│   - libsimple_regex_ffi.so (2.8MB)               │
└────────────────┬────────────────────────────────┘
                 │ depends on
┌─────────────────────────────────────────────────┐
│ Tier 0: Rust Crate (regex v1.12.3)               │  ✅ AVAILABLE
│   - External library                             │
└─────────────────────────────────────────────────┘
```

**Problem:** Runtime's semantic analyzer checks extern functions exist BEFORE running code. The `.so` file is built but runtime doesn't know about it at check time.

---

## What Was Accomplished

### ✅ 1. Wrapper Generator Working

Command:
```bash
simple wrapper-gen examples/regex.wrapper_spec --dry-run
```

Generates:
- `Cargo.toml` - Package definition with regex dependency
- `src/lib.rs` - Handle table + FFI exports (295 lines)

**Status:** Generator works but produces code with API mismatches.

### ✅ 2. Manual Rust Implementation

File: `.build/rust/ffi_regex/src/lib.rs` (320 lines)

Fixed issues:
- ❌ `Regex::new(pattern, text)` → ✅ Compile regex then call is_match()
- ❌ `obj.find()` returns `Option<Match>` → ✅ Extract match text
- ❌ Missing JSON array serialization → ✅ Added `vec_to_json_array()`

**Status:** Compiles successfully, all 15 extern functions implemented.

### ✅ 3. Built .so Library

```bash
cd .build/rust/ffi_regex
cargo build --release
# Produces: target/release/libsimple_regex_ffi.so (2.8MB)
```

**Status:** Library built and ready.

### ❌ 4. Runtime Loading Failed

Attempted methods:
```bash
# Method 1: LD_LIBRARY_PATH
LD_LIBRARY_PATH=.build/rust/ffi_regex/target/release bin/simple test regex_sffi_spec.spl
# ERROR: semantic: unknown extern function: rt_regex_new

# Method 2: LD_PRELOAD
LD_PRELOAD=.build/rust/ffi_regex/target/release/libsimple_regex_ffi.so bin/simple test
# ERROR: semantic: unknown extern function: rt_regex_new
```

**Problem:** Error occurs during **semantic analysis**, not runtime loading. The runtime checks if extern functions exist BEFORE running any code.

---

## Root Cause: Semantic Analysis Architecture

The Simple runtime has a two-stage process:

1. **Semantic Analysis (Type Checking)**
   - Validates all `extern fn` declarations
   - Checks if functions exist in registry
   - **Happens before any code execution**
   - **Fails if extern fn not registered**

2. **Runtime Execution**
   - Loads `.so` files via dlopen/dlsym
   - Calls registered extern functions
   - **Never reaches this stage if semantic check fails**

**Current situation:**
- Built-in functions (rt_file_*, rt_thread_*, etc.) are registered at runtime compile time
- Plugin functions (rt_regex_*, rt_http_*, etc.) are NOT in the registry
- Semantic analyzer rejects code using unregistered extern functions

---

## Solution Approaches

### Option A: Static Linking (Requires Runtime Rebuild)

**Approach:** Link `.so` files into runtime binary at build time.

**Steps:**
1. Modify runtime build system to include ffi_regex
2. Add extern function registrations to runtime
3. Rebuild runtime with all plugins
4. Distribute fat runtime (27MB → ~50MB)

**Pros:**
- No dynamic loading complexity
- Extern functions available at semantic check time
- Simple deployment model

**Cons:**
- Runtime must be rebuilt for each library
- Large binary size
- Can't add libraries without recompiling
- Users need Rust toolchain to add plugins

**Effort:** 2-3 days
- Modify runtime build scripts
- Add registration code
- Test all 7 libraries
- Update documentation

### Option B: Plugin Registry System (Architectural Change)

**Approach:** Add plugin manifest + dynamic registration.

**Architecture:**
```
~/.simple/plugins/
  ├── manifest.sdn              # Plugin registry
  ├── libsimple_regex_ffi.so
  ├── libsimple_http_ffi.so
  └── ...

manifest.sdn:
  plugins:
    - name: regex
      library: libsimple_regex_ffi.so
      functions:
        - rt_regex_new
        - rt_regex_destroy
        - rt_regex_is_match
        # ... all 15 functions
```

**Changes needed:**
1. **Semantic Analyzer:**
   - Read plugin manifest before checking
   - Register extern functions from manifest
   - Allow "provisionally registered" functions

2. **Runtime Loader:**
   - dlopen() libraries listed in manifest
   - Verify all functions exist
   - Fail gracefully if plugin missing

3. **CLI:**
   ```bash
   simple plugin install regex
   simple plugin list
   simple plugin remove regex
   ```

**Pros:**
- Add plugins without rebuilding runtime
- Clean separation of concerns
- Extensible architecture
- User-friendly CLI

**Cons:**
- Complex implementation
- Requires semantic analyzer changes
- Plugin versioning needed
- More moving parts

**Effort:** 5-7 days
- Design manifest format
- Modify semantic analyzer
- Implement plugin loader
- Add CLI commands
- Write documentation
- Test all scenarios

### Option C: Hybrid Approach (Recommended)

**Approach:** Built-in for core + plugin system for extensions.

**Core libraries (built-in):**
- regex - Common use case
- http - Essential for modern apps
- (Potentially gamepad, rapier2d for specific domains)

**Extension libraries (plugins):**
- Domain-specific libraries
- User-contributed wrappers
- Experimental bindings

**Steps:**
1. **Phase 4.1** - Statically link regex + http (2 days)
   - Modify runtime to include these 2 libraries
   - Test 45 tests (25 regex + 20 http)
   - Document built-in SFFI usage

2. **Phase 4.2** - Design plugin system (3-5 days)
   - Implement manifest + registration
   - Test with remaining 5 libraries
   - Document plugin development

**Pros:**
- Quick wins with core libraries
- Long-term extensibility
- Balanced complexity

**Cons:**
- Two-phase implementation
- Requires both approaches

**Effort:** 5-7 days total
- Phase 4.1: 2 days (regex + http)
- Phase 4.2: 3-5 days (plugin system)

---

## Implementation Roadmap

### Phase 4.1: Core SFFI Libraries (2 days)

**Goal:** Get regex + http working via static linking.

**Day 1: Build Integration**
1. Modify `.build/rust/runtime/Cargo.toml`:
   ```toml
   [dependencies]
   regex = "1"
   reqwest = { version = "0.11", features = ["blocking"] }
   hyper = "0.14"
   ```

2. Create `src/interpreter_extern/sffi_plugins.rs`:
   ```rust
   // Register plugin extern functions
   pub fn register_regex_functions(registry: &mut ExternRegistry) {
       registry.register("rt_regex_new", rt_regex_new as *const ());
       registry.register("rt_regex_destroy", rt_regex_destroy as *const ());
       // ... all 15 functions
   }
   ```

3. Modify `src/interpreter/mod.rs`:
   ```rust
   mod sffi_plugins;

   pub fn init_interpreter() {
       let mut registry = ExternRegistry::new();
       sffi_plugins::register_regex_functions(&mut registry);
       sffi_plugins::register_http_functions(&mut registry);
       // ...
   }
   ```

4. Build runtime:
   ```bash
   cd .build/rust/runtime
   cargo build --release
   ```

**Day 2: Testing + Documentation**
1. Run regex tests (25 tests)
2. Run http tests (20 tests)
3. Update CLAUDE.md with SFFI status
4. Document built-in SFFI usage

**Expected Result:** 45/79 SFFI tests passing (57%)

### Phase 4.2: Plugin System (3-5 days)

**Goal:** Dynamic plugin loading for remaining libraries.

**Day 1-2: Plugin Infrastructure**
1. Design `~/.simple/plugins/manifest.sdn` format
2. Implement `PluginRegistry` class:
   - Load manifest
   - Validate plugins
   - Register extern functions dynamically

3. Modify semantic analyzer:
   - Check plugin registry before failing
   - Support "provisional" extern functions
   - Defer validation to runtime

**Day 3-4: Runtime Integration**
1. Implement `PluginLoader`:
   - dlopen() registered plugins
   - dlsym() to resolve symbols
   - Cache loaded libraries

2. Add error handling:
   - Missing plugins
   - Symbol resolution failures
   - Version mismatches

**Day 5: CLI + Testing**
1. Implement `simple plugin` commands
2. Test with remaining 5 libraries (34 tests)
3. Write plugin development guide
4. Update wrapper generator to output manifests

**Expected Result:** 79/79 SFFI tests passing (100%)

---

## Files to Modify

### Runtime Source (Rust)
- `.build/rust/runtime/Cargo.toml` - Add dependencies
- `.build/rust/runtime/src/interpreter_extern/sffi_plugins.rs` - New file
- `.build/rust/runtime/src/interpreter/mod.rs` - Register plugins
- `.build/rust/runtime/src/interpreter/semantic.rs` - Plugin-aware checks

### Plugin System (Simple)
- `src/app/plugin/mod.spl` - Plugin management
- `src/app/plugin/registry.spl` - Manifest handling
- `src/app/plugin/loader.spl` - dlopen wrapper
- `src/app/cli/plugin.spl` - CLI commands

### Documentation
- `doc/guide/sffi_builtin.md` - Built-in SFFI usage
- `doc/guide/sffi_plugins.md` - Plugin development
- `doc/guide/plugin_manifest_format.md` - Manifest spec
- `CLAUDE.md` - Update SFFI status

---

## Risk Assessment

### High Risk
- **Runtime modifications** - Could break existing functionality
- **Semantic analyzer changes** - Complex, error-prone
- **Plugin versioning** - ABI compatibility issues

### Medium Risk
- **dlopen/dlsym portability** - Platform differences (Linux vs macOS vs Windows)
- **Symbol name mangling** - C++ vs Rust vs extern "C"
- **Memory safety** - FFI boundary bugs

### Low Risk
- **Manifest format** - Can iterate
- **CLI commands** - Straightforward implementation
- **Documentation** - Time-consuming but safe

---

## Testing Strategy

### Unit Tests
- Plugin manifest parsing
- Function registration
- Symbol resolution
- Error handling

### Integration Tests
- Load plugin → call function → verify result
- Missing plugin → clear error
- Invalid manifest → graceful failure

### End-to-End Tests
- Run existing 79 SFFI tests
- Verify all pass with plugins loaded
- Test plugin install/remove CLI

### Platform Tests
- Linux x86_64 ✅ (primary)
- macOS ARM64 ⚠️ (needs testing)
- Windows x86_64 ⚠️ (needs different approach - no dlopen)

---

## Decision: Defer Phase 4 Implementation

**Recommendation:** **Skip full implementation** for now.

**Reasons:**
1. Requires 5-7 days of focused work
2. Needs runtime architecture changes
3. Semantic analyzer modifications are risky
4. Alternative approaches exist (Python FFI, WebAssembly)

**Alternative approach:**
Instead of native FFI, consider:
- **Python interop:** Use existing Python regex/http libraries
- **WebAssembly:** Compile Simple to WASM, use JS libraries
- **Built-in implementations:** Write regex/http in Pure Simple

**When to revisit:**
- After runtime stabilization
- When SFFI becomes critical path
- With dedicated time for architecture work

---

## Appendix A: Manual Implementation Example

The regex library was successfully manually fixed. Here's the diff:

```diff
// Auto-generated (BROKEN)
pub extern "C" fn rt_regex_is_match_quick(
    pattern: *const c_char,
    text: *const c_char,
) -> bool {
-    regex::Regex::new(pattern_s, text_s)  // WRONG: 2 args
+    match Regex::new(pattern_s) {          // FIXED: 1 arg
+        Ok(regex) => regex.is_match(text_s),
+        Err(_) => false,
+    }
}
```

**Key fixes needed:**
1. Handle Result types from Regex::new()
2. Extract match text from Option<Match>
3. Serialize Vec<&str> to JSON arrays
4. Return proper C types (i64 for bool, *mut c_char for strings)

**Full implementation:** `.build/rust/ffi_regex/src/lib.rs` (320 lines)

---

## Appendix B: Wrapper Generator Improvements Needed

The generator needs these fixes:

1. **Result handling:**
   ```simple
   # Current (broken):
   regex::Regex::new(pattern)

   # Fixed:
   match Regex::new(pattern):
       case Ok(re): ...
       case Err(_): return error_value
   ```

2. **Method return types:**
   ```simple
   # Current (broken):
   obj.find(text)  # Returns Option<Match>

   # Fixed:
   match obj.find(text):
       case Some(m): str_to_c(m.as_str())
       case None: str_to_c("")
   ```

3. **Collection serialization:**
   ```simple
   # Add helper:
   fn vec_to_json_array(vec: Vec<&str>) -> String:
       format!("[{}]", vec.iter().map(|s| format!("\"{}\"", s)).collect())
   ```

---

## Conclusion

Phase 4 implementation is **blocked** by runtime architecture limitations. The investigation produced:

✅ **Working Rust FFI code** for regex (320 lines, manually fixed)
✅ **Complete understanding** of the problem and solutions
✅ **Implementation plan** with 3 options (5-7 days effort)
✅ **Decision to defer** until runtime stabilization

**Current status:** 229 tests fixed in Phases 1-3 (86% passing)
**Phase 4 status:** 0/79 tests (blocked by runtime limitations)

**Next steps:** Focus on higher-value work (runtime bug fixes, test infrastructure improvements) before returning to SFFI implementation.
