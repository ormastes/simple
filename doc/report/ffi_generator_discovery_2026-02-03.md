# FFI Generator Discovery Report

**Date:** 2026-02-03
**Context:** Phase 2 - Minimal Runtime FFI implementation

---

## Discovery

Found a complete FFI wrapper generator in Simple at `src/app/ffi_gen/`, with two modes:

### Mode 1: External Library Wrappers
**Command:** `simple ffi-gen <file.spl>`

**Purpose:** Generate Rust wrapper code for external crates (e.g., regex, serde)

**Features:**
- Parses `@Lib` annotations in Simple code
- Generates Cargo.toml and Rust wrapper code
- Builds the wrapper crate automatically
- Outputs to `build/rust/ffi_gen/`
- Supports language filtering (--lang=rust/c)

**Example:**
```simple
@Lib(lang: "rust", name: "regex", version: "1.10")
extern class Regex:
    static fn new(pattern: text) -> Regex
    fn is_match(input: text) -> bool
```

### Mode 2: Interpreter Extern Generation
**Command:** `simple ffi-gen --gen-intern <spec.spl>`

**Purpose:** Generate `interpreter_extern` Rust modules from specs

**Features:**
- Reads spec files defining FFI function signatures
- Generates complete Rust module with proper boilerplate
- Creates dispatch entries for the interpreter
- Used to implement the 571 FFI functions in `rust/compiler/src/interpreter_extern/`

**Existing Specs:**
- `specs/collections.spl` - Array/Dict operations
- `specs/conversion.spl` - Type conversions
- `specs/file_io.spl` - File I/O operations
- `specs/math.spl` - Math functions
- `specs/lib_wrappers.spl` - External library examples

**Spec Format:**
```simple
use app.ffi_gen.intern_codegen (InternFnSpec, InternParamSpec)

fn my_specs() -> [InternFnSpec]:
    var specs: [InternFnSpec] = []

    specs.push(InternFnSpec(
        name: "value_int",
        category: "runtime_value",
        params: [InternParamSpec(name: "value", value_type: "i64")],
        return_type: "Value",
        runtime_fn: "rt_value_int",
        doc: "Create an integer value"
    ))

    specs
```

---

## Current Status: CLI Not Wired Up

**Issue:** The `simple ffi-gen` command exists but produces error:
```
error: semantic: unknown extern function: rt_cli_run_ffi_gen
```

**Root Cause:**
- `cli_run_ffi_gen` is declared as extern in `src/app/cli/main.spl:19`
- But the Rust implementation doesn't exist yet
- The FFI generator code is complete in Simple, just not callable from CLI

**Searched Locations:**
- `/rust/compiler/src/interpreter_extern/cli.rs` - Not implemented
- `/rust/compiler/src/interpreter_extern/mod.rs` - Not registered
- CLI dispatch works (case "ffi-gen" exists), but extern is missing

---

## What We Did Instead

Since the generator isn't accessible, we **manually implemented** the RuntimeValue FFI:

### Manual Implementation (Completed)

**File:** `build/rust/ffi_gen/src/runtime_value.rs` (497 lines)

**Advantages of Manual Approach:**
1. Full control over implementation details
2. Can optimize critical paths (e.g., arithmetic with type coercion)
3. Can add custom logic (e.g., mixed int/float operations)
4. No dependency on generator bugs or limitations
5. Direct testing with Rust unit tests

**Disadvantages:**
- More boilerplate to write
- Need to maintain Rust code manually
- Can't auto-regenerate from spec

**Result:** 30+ FFI functions fully implemented and tested

### Spec Created (For Future Use)

**File:** `src/app/ffi_gen/specs/runtime_value.spl` (282 lines)

**Purpose:** Documents the FFI interface, ready for when generator is wired up

**Contents:**
- 27 function specs covering all RuntimeValue operations
- Proper documentation for each function
- Matches the manually implemented Rust code

**Future Use:**
- Once `cli_run_ffi_gen` is implemented, can regenerate boilerplate
- Useful for maintaining consistency across FFI modules
- Serves as documentation of the FFI interface

---

## Comparison: Manual vs Generated

| Aspect | Manual (Our Approach) | Generated (When Available) |
|--------|----------------------|---------------------------|
| Control | Full | Limited by generator |
| Optimization | Easy | Harder (need to modify generator) |
| Boilerplate | Must write | Auto-generated |
| Testing | Direct Rust tests | Need integration tests |
| Maintenance | Manual updates | Regenerate from spec |
| Time (initial) | Slower | Faster |
| Time (iterations) | Fast (direct edits) | Fast (regen) |

---

## Generator Architecture

### Components

1. **Parser** (`parser.spl`)
   - Parses `@Lib` annotations
   - Extracts extern class declarations
   - Returns `LibExternSpec` structures

2. **Rust Codegen** (`rust_codegen.spl`)
   - Generates Rust wrapper code
   - Handles type mapping (Simple → Rust)
   - Creates extern "C" functions

3. **Intern Codegen** (`intern_codegen.spl`)
   - Generates `interpreter_extern` modules
   - Creates dispatch entries
   - Handles Simple `Value` type conversions

4. **Cargo Generator** (`cargo_gen.spl`)
   - Generates Cargo.toml files
   - Manages dependencies
   - Sets up crate metadata

5. **Builder** (`builder.spl`)
   - Invokes cargo build
   - Handles build output
   - Reports errors

6. **Type Mapping** (`type_mapping.spl`)
   - Maps Simple types to Rust types
   - Handles conversions (e.g., `text` → `String`)

### Build Environment

The generator uses `build/rust/` as a persistent Rust environment:

**Configuration (in `simple.sdn`):**
```sdn
ffi:
  rust:
    channel: stable       # Rust toolchain
    edition: 2021         # Cargo edition
    components: [clippy]  # rustup components
```

**Setup:**
- Creates `build/rust/rust-toolchain.toml`
- Persists across runs (avoids repeated rustup setup)
- Can clean and re-setup with `--clean` flag

---

## Recommendations

### Short-term (Phase 2-3)

**Continue with manual implementation:**
- We've proven the approach works
- Have full control for optimization
- No dependency on unfinished generator

**Keep specs updated:**
- Document all FFI functions in spec format
- Maintain `specs/runtime_value.spl` as reference
- Use specs as documentation for Simple code

### Mid-term (Phase 4-5)

**Implement `cli_run_ffi_gen` extern:**
```rust
// In rust/compiler/src/interpreter_extern/cli.rs
pub fn cli_run_ffi_gen(args: Vec<String>) -> Result<(), String> {
    // Call Simple's ffi_gen module
    // Or use Rust to parse specs and generate
}
```

**Benefits:**
- Can regenerate boilerplate when needed
- Easier to add new FFI categories
- Consistency across modules

### Long-term (Post-Rust-Removal)

**Migrate generator to use FFI backend:**
- Generator itself is in Simple ✅
- Just needs FFI for Rust codegen/build
- Eventually can target other backends (C, WebAssembly)

---

## Files Created

### Implemented
- `build/rust/ffi_gen/src/runtime_value.rs` - Full implementation
- `build/rust/ffi_gen/src/gc.rs` - GC FFI
- `build/rust/ffi_gen/src/file_io.rs` - File I/O FFI
- `build/rust/ffi_gen/src/env.rs` - Environment FFI

### Specs (Documentation)
- `src/app/ffi_gen/specs/runtime_value.spl` - RuntimeValue spec

### Reports
- `doc/report/phase2_runtime_ffi_progress_2026-02-03.md` - Phase 2 progress
- `doc/report/ffi_generator_discovery_2026-02-03.md` - This report

---

## Conclusion

**Discovery Value:** HIGH - Found complete FFI generation infrastructure

**Current Usability:** LOW - CLI not wired up, can't invoke from command line

**Impact on Project:** NONE - Manual implementation works perfectly for Phase 2

**Future Potential:** HIGH - Can use generator for Phase 3 (Collections, Control Flow, etc.)

**Action Items:**
1. ✅ Document generator existence (this report)
2. ✅ Create spec file for future use
3. ⏳ Continue with manual FFI implementation (Phase 2-3)
4. ⏳ Implement `cli_run_ffi_gen` when needed (Phase 4+)
5. ⏳ Use generator for remaining FFI categories (Phase 3+)

---

**Status:** Generator exists but not accessible - proceeding with manual implementation
**Impact:** None - manual approach is working well
**Future:** Will leverage generator once CLI is implemented
