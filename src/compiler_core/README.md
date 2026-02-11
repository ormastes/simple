# Core Simple Implementation

This directory contains the **desugared** version of the Full Simple compiler,
compatible with the seed compiler (seed/seed.cpp).

## Constraints

Core Simple has these restrictions:

- ❌ **No `impl` blocks** - use module-level functions instead
- ❌ **No generics** - monomorphize to concrete types (no `<T>`)
- ❌ **No closures** - lambda-lift to top-level functions
- ❌ **No `Option<T>`** - use `has_value: bool` + `value_field` pattern
- ❌ **No multi-line boolean expressions** - use intermediate variables
- ❌ **No trait constraints** - direct function calls only
- ✅ **Only**: i64, f64, text, bool, arrays, simple structs, simple enums

## Relationship to compiler/

Files in `compiler/` (Full Simple) are transformed to `compiler_core/` (Core Simple) via desugaring.

### Example Transformation

**Full Simple (`compiler/backend/llvm_type_mapper.spl`):**
```simple
impl TypeMapper for LlvmTypeMapper:
    fn map_primitive<T>(ty: T) -> text:
        match ty:
            case I64: "i64"
            case F64: "double"
```

**Core Simple (`compiler_core/backend/llvm_type_mapper.spl`):**
```simple
fn llvmtypemapper_map_primitive(mapper: LlvmTypeMapper, ty: PrimitiveType) -> text:
    match ty:
        case I64: "i64"
        case F64: "double"
```

See DESUGARING_PLAN.md for complete transformation rules.

## Bootstrap Role

This code is the **first stage** of the bootstrap process:

1. `seed.cpp` (C++ seed) compiles **Core Simple** → produces bootstrap compiler
2. Bootstrap compiler compiles **Full Simple** → produces full compiler
3. Full compiler compiles itself → self-hosting complete

## Files

Key modules:
- `ast.spl`, `lexer.spl`, `parser.spl` - Frontend (parsing .spl files)
- `mir.spl`, `mir_lowering.spl` - Middle-end (MIR generation)
- `backend/` - Code generation for LLVM, CUDA, WASM, etc.
- `linker/` - Object file linking and SMF format
- `monomorphize/` - Generic instantiation (for Full Simple features)

## Development

When modifying Full Simple code in `compiler/`, you must also update the corresponding
desugared code in `compiler_core/`. Use the desugaring tools in `src/tools/`:

```bash
python3 src/tools/desugarer.py src/compiler/backend/llvm_type_mapper.spl
# Generates desugared version for compiler_core/
```

## DO NOT

- ❌ Add generics, traits, or closures to this code
- ❌ Merge with `compiler/` directory
- ❌ Use multi-line boolean expressions
- ❌ Assume runtime features work (no try/catch, limited closures)
