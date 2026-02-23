# Backend Instruction Completeness - Next Steps Guide

**Quick Reference for Completing Phases 2-4**

---

## Prerequisites: Fix Parser

Before ANY other work can proceed, the Simple parser must be fixed.

### Problem

Current Simple parser code (in `/rust/parser/`) does not support array types `[T]` in enum variant payloads.

**Failing Code:**
```simple
enum MirTestInst:
    ArrayLit(VReg, [VReg])  # <-- Parser error
```

### Solution Options

#### Option A: Support Array Syntax

Modify `/rust/parser/src/parser.rs` to accept:
```rust
// In parse_enum_variant() function:
// Allow Type::Array in variant payload positions
```

Test case:
```simple
enum Test:
    WithArray([i32])       # Should parse
    WithMultiple(i32, [text], [bool])  # Should parse
```

#### Option B: Use Generic List Type

If `List<T>` already works, use that:
```simple
enum MirTestInst:
    ArrayLit(VReg, List<VReg>)  # Try this
```

Test if `List<T>` works in enums:
```bash
echo 'enum Test: Var(List<i32>)' > /tmp/test.spl
./rust/target/debug/simple_runtime /tmp/test.spl
```

#### Option C: Helper Class Workaround

```simple
class VRegList:
    regs: [VReg]

enum MirTestInst:
    ArrayLit(VReg, VRegList)  # Wrapper works
```

**Recommended:** Try Option B first (quickest), then Option A if needed.

---

## Phase 2: Backend Integration (4-6 hours)

### 2.1: Create Backend FFI (1-2 hours)

**File:** `/src/compiler/backend/backend_ffi.spl`

```simple
# FFI bindings to Rust compiler backends

extern fn compile_mir_cranelift(mir_json: text) -> Result<text, text>
extern fn compile_mir_llvm(mir_json: text) -> Result<text, text>
extern fn compile_mir_vulkan(mir_json: text) -> Result<text, text>

class BackendCompiler:
    static fn compile_with_cranelift(mir: MirModule) -> Result<CompiledCode, text>:
        val json = mir.to_json()
        match compile_mir_cranelift(json):
            Ok(bytecode): Ok(CompiledCode(backend: "cranelift", bytecode: bytecode))
            Err(e): Err(e)

    static fn compile_with_llvm(mir: MirModule) -> Result<CompiledCode, text>:
        val json = mir.to_json()
        match compile_mir_llvm(json):
            Ok(bytecode): Ok(CompiledCode(backend: "llvm", bytecode: bytecode))
            Err(e): Err(e)

    static fn compile_with_vulkan(mir: MirModule) -> Result<CompiledCode, text>:
        val json = mir.to_json()
        match compile_mir_vulkan(json):
            Ok(bytecode): Ok(CompiledCode(backend: "vulkan", bytecode: bytecode))
            Err(e): Err(e)

struct CompiledCode:
    backend: text
    bytecode: text
```

### 2.2: Implement Rust FFI Functions (2-3 hours)

**File:** `/rust/compiler/src/interpreter_extern/backend_compilation.rs`

```rust
use crate::error::CompileError;
use crate::value::Value;

pub fn compile_mir_cranelift(args: &[Value]) -> Result<Value, CompileError> {
    let mir_json = match args.get(0) {
        Some(Value::Str(s)) => s,
        _ => return Err(CompileError::type_error("Expected MIR JSON string")),
    };

    // Parse MIR JSON
    // Call Cranelift backend
    // Return bytecode or error

    Err(CompileError::not_implemented("Cranelift compilation"))
}

pub fn compile_mir_llvm(args: &[Value]) -> Result<Value, CompileError> {
    // Similar to cranelift
    Err(CompileError::not_implemented("LLVM compilation"))
}

pub fn compile_mir_vulkan(args: &[Value]) -> Result<Value, CompileError> {
    // Similar to cranelift
    Err(CompileError::not_implemented("Vulkan compilation"))
}
```

**Register in** `/rust/compiler/src/interpreter_extern/mod.rs`:

```rust
pub mod backend_compilation;

// In call_extern_function():
"compile_mir_cranelift" => backend_compilation::compile_mir_cranelift(&evaluated),
"compile_mir_llvm" => backend_compilation::compile_mir_llvm(&evaluated),
"compile_mir_vulkan" => backend_compilation::compile_mir_vulkan(&evaluated),
```

### 2.3: Test Backend Integration (1 hour)

```bash
./rust/target/debug/simple_runtime test test/compiler/backend/
```

Expected: Tests should run (may fail, but shouldn't timeout).

---

## Phase 3: Documentation Generation (6-8 hours)

### 3.1: Capability Tracker (2-3 hours)

**File:** `/src/compiler/backend/capability_tracker.spl`

See `/doc/report/backend_completeness_implementation_report.md` for full implementation template.

Key methods:
```simple
class BackendCapabilities:
    static fn for_cranelift() -> BackendCapabilities
    static fn for_llvm() -> BackendCapabilities
    static fn for_vulkan() -> BackendCapabilities
    static fn detect_support_from_source(file_path: text) -> Dict<text, InstructionSupport>
    fn to_markdown() -> text
```

### 3.2: Matrix Builder (2-3 hours)

**File:** `/src/compiler/backend/matrix_builder.spl`

Key methods:
```simple
class BackendMatrixBuilder:
    static fn new() -> BackendMatrixBuilder
    fn build_matrix() -> BackendMatrix
    fn to_markdown() -> text
    fn generate_statistics() -> BackendStats
```

### 3.3: Documentation Generator (1-2 hours)

**File:** `/scripts/generate_backend_docs.spl`

```simple
fn main(args: [text]):
    val cmd = if args.len > 0: args[0] else: "all"

    match cmd:
        "matrix": generate_matrix()
        "capabilities": generate_capabilities()
        "stats": generate_stats()
        "all": generate_all()
        _: print("Usage: simple scripts/generate_backend_docs.spl [matrix|capabilities|stats|all]")

fn generate_matrix():
    val builder = BackendMatrixBuilder.new()
    val markdown = builder.to_markdown()
    File.write("doc/backend/BACKEND_SUPPORT_MATRIX.md", markdown)

fn generate_capabilities():
    for backend_name in ["cranelift", "llvm", "vulkan"]:
        val caps = BackendCapabilities.for_{backend_name}()
        val markdown = caps.to_markdown()
        File.write("doc/backend/{backend_name}_capabilities.md", markdown)

fn generate_stats():
    val builder = BackendMatrixBuilder.new()
    val stats = builder.generate_statistics()
    val json = stats.to_json()
    File.write("doc/backend/stats.json", json)
    print(stats.summary())

fn generate_all():
    generate_matrix()
    generate_capabilities()
    generate_stats()
```

### 3.4: Test Documentation (1 hour)

```bash
./rust/target/debug/simple_runtime scripts/generate_backend_docs.spl all

# Verify output
ls -la doc/backend/
cat doc/backend/BACKEND_SUPPORT_MATRIX.md
```

---

## Phase 4: DSL-Based Code Generation (8-12 hours)

### 4.1: Design IR DSL Syntax (1-2 hours)

**File:** `/doc/design/ir_dsl_syntax_v2.md`

Example syntax:
```irdsl
# Integer constants
instruction ConstInt:
    operands: [dest: vreg, value: i64]
    backends: [cranelift, llvm, vulkan]
    category: constants

    cranelift:
        emit "iconst {dest}, {value}"

    llvm:
        emit "{dest} = iconstant i64 {value}"

    vulkan:
        emit "OpConstant %i64 {dest} {value}"
```

### 4.2: Implement DSL Parser (4-5 hours)

**File:** `/src/compiler/irdsl/parser.spl`

```simple
class IRDSLParser:
    me parse_file(path: text) -> [InstructionDef]:
        val content = File.read(path)
        val tokens = self.tokenize(content)
        self.parse_tokens(tokens)

    me tokenize(content: text) -> [Token]:
        # Lexer implementation

    me parse_tokens(tokens: [Token]) -> [InstructionDef]:
        # Parser implementation

struct InstructionDef:
    name: text
    operands: [Operand]
    backends: [text]
    category: text
    emit_code: Dict<text, text>
```

### 4.3: Implement Code Generator (3-4 hours)

**File:** `/src/compiler/irdsl/codegen.spl`

```simple
class IRDSLCodeGen:
    me generate_rust(defs: [InstructionDef]) -> text:
        val output = []
        output.push("// Auto-generated from instructions.irdsl")
        output.push("")

        for def in defs:
            output.push(self.generate_instruction(def))

        output.join("\n")

    me generate_instruction(def: InstructionDef) -> text:
        """
        Generate Rust match arm like:
        MirInst::ConstInt { dest, value } => {
            // Backend-specific code
        }
        """
```

### 4.4: Create Sample DSL (1-2 hours)

**File:** `/instructions.irdsl`

Define 15-20 representative instructions covering:
- Constants (ConstInt, ConstFloat, ConstBool, ConstString)
- Arithmetic (Add, Sub, Mul, Div, Mod)
- Comparison (Eq, Lt, Gt)
- Control flow (Jump, Branch, Ret)
- Memory (Load, Store, Copy)
- Collections (ArrayLit, IndexGet)
- SIMD (VecLit, VecSum)
- GPU (GpuGlobalId, GpuBarrier)

### 4.5: Test Code Generation (1 hour)

```bash
# Parse DSL
./rust/target/debug/simple_runtime src/compiler/irdsl/test_parser.spl

# Generate code
./rust/target/debug/simple_runtime src/compiler/irdsl/test_codegen.spl

# Verify output
cat generated_instructions.rs

# Try compiling generated code
cp generated_instructions.rs rust/compiler/src/codegen/
cargo +nightly build
```

---

## Verification Checklist

### Phase 1 (Already Complete)
- [x] All FFI functions implemented
- [x] Functions registered in mod.rs
- [x] Runtime builds successfully
- [x] Binary at `/rust/target/debug/simple_runtime`

### Phase 2 (After Parser Fix)
- [ ] `backend_ffi.spl` created
- [ ] 3 Rust FFI functions implemented
- [ ] Functions registered in mod.rs
- [ ] Tests run without parse errors
- [ ] Can compile simple MIR to bytecode

### Phase 3
- [ ] `capability_tracker.spl` created
- [ ] `matrix_builder.spl` created
- [ ] `generate_backend_docs.spl` created
- [ ] Documentation generates successfully
- [ ] Files created in `doc/backend/`

### Phase 4
- [ ] DSL syntax design document created
- [ ] `irdsl/parser.spl` created
- [ ] `irdsl/codegen.spl` created
- [ ] `instructions.irdsl` created with 15+ instructions
- [ ] Generated Rust code compiles
- [ ] Generated code functionally equivalent to hand-written

---

## Testing Strategy

### Unit Tests
```bash
# Test each phase independently
./rust/target/debug/simple_runtime test test/compiler/backend/backend_ffi_spec.spl
./rust/target/debug/simple_runtime test test/compiler/backend/capability_tracker_spec.spl
./rust/target/debug/simple_runtime test test/compiler/backend/matrix_builder_spec.spl
./rust/target/debug/simple_runtime test test/compiler/backend/irdsl_parser_spec.spl
```

### Integration Tests
```bash
# Test full workflow
./rust/target/debug/simple_runtime test test/compiler/backend/

# Should show:
# - All tests pass
# - No timeouts
# - Coverage reports generated
```

### End-to-End Test
```bash
# Generate docs
./rust/target/debug/simple_runtime scripts/generate_backend_docs.spl all

# Compile with generated code
cargo +nightly build --release

# Use LLVM backend
./rust/target/release/simple_runtime compile --backend=llvm example.spl
```

---

## Time Estimates

| Task | Hours | Dependencies |
|------|-------|--------------|
| Fix parser | 2-4 | None |
| Phase 2 impl | 4-6 | Parser fix |
| Phase 3 impl | 6-8 | Phase 2 |
| Phase 4 impl | 8-12 | Phase 3 |
| Testing/debug | 4-6 | All phases |
| Documentation | 2-3 | All phases |
| **TOTAL** | **26-39** | - |

---

## Common Issues

### Parse Errors
- **Problem:** `expected pattern, found Vec`
- **Solution:** Fix parser or use List<T>/helper classes

### Import Errors
- **Problem:** `undefined symbol rt_*`
- **Solution:** Check FFI registration in mod.rs

### Build Errors
- **Problem:** `feature(linkage)` error
- **Solution:** Use `cargo +nightly build`

### Binary Path
- **Problem:** Using old stale binary
- **Solution:** Use `./rust/target/debug/simple_runtime`

### Timeout
- **Problem:** Tests timeout after 120s
- **Solution:** Tests have parse errors, fix parser first

---

## Quick Commands

```bash
# Build
cd /home/ormastes/dev/pub/simple/rust
cargo +nightly build

# Test
./rust/target/debug/simple_runtime test test/compiler/backend/

# Generate docs
./rust/target/debug/simple_runtime scripts/generate_backend_docs.spl all

# Check FFI registration
grep "rt_file_read_text" rust/compiler/src/interpreter_extern/mod.rs

# Verify binary
ls -lh rust/target/debug/simple_runtime

# Test parser fix
echo 'enum Test: Var([i32])' > /tmp/test.spl
./rust/target/debug/simple_runtime /tmp/test.spl
```

---

**Ready to continue?** Start with fixing the parser, then proceed through Phases 2-4 in order.
