# Backend Shared Architecture - Refactoring Design

**Date**: 2026-02-05
**Status**: Design Proposal
**Goal**: Eliminate duplication, create proper abstractions, simplify adding new backends

---

## EXECUTIVE SUMMARY

### Current Problems
- **1,500+ lines of duplicated code** across 4 backends
- **No shared type mapping** - each backend reimplements mir_type_to_X()
- **Manual dispatch** via match statements instead of polymorphism
- **Mixed concerns** - interpreter values mixed with FFI pointers
- **Hard to extend** - adding new backend requires 500-1000 lines (70% duplication)

### Proposed Solution
Create **3-tier architecture**:
1. **Common Layer**: Shared utilities (type mapping, evaluation, errors)
2. **Abstract Layer**: Traits and base implementations
3. **Backend Layer**: Specialized implementations (Cranelift, LLVM, etc.)

### Expected Benefits
- **Reduce code by 30%** (1,500+ lines eliminated)
- **Faster backend development** (new backend ~200 lines vs ~800 lines)
- **Better testing** (shared logic tested once)
- **Consistent behavior** (same patterns across backends)

---

## 1. CURRENT ARCHITECTURE (BEFORE)

```
┌─────────────────────────────────────────────────────────────┐
│                     Compiler Pipeline                        │
│  Lexer → Parser → Type Check → HIR → MIR → Backend          │
└──────────────────────────────────┬───────────────────────────┘
                                   │
         ┌─────────────────────────┼─────────────────────────┐
         │                         │                         │
    ┌────▼────┐              ┌────▼────┐              ┌────▼────┐
    │Cranelift│              │  LLVM   │              │Interpret│
    │ Backend │              │ Backend │              │ Backend │
    └─────────┘              └─────────┘              └─────────┘
         │                         │                         │
    DUPLICATED               DUPLICATED               DUPLICATED
    Type mapping             Type mapping             Type mapping
    Expression eval          Expression eval          Expression eval
    Literal conversion       Literal conversion       Literal conversion
    Error handling           Error handling           Error handling
```

**Problem**: Each backend reimplements common patterns independently.

---

## 2. PROPOSED ARCHITECTURE (AFTER)

```
┌─────────────────────────────────────────────────────────────┐
│                     Compiler Pipeline                        │
│  Lexer → Parser → Type Check → HIR → MIR → BackendFactory   │
└──────────────────────────────────────┬───────────────────────┘
                                       │
                     ┌─────────────────┴─────────────────┐
                     │       Common Backend Layer        │
                     │  - TypeMapper (trait)              │
                     │  - ExpressionEvaluator (base)      │
                     │  - LiteralConverter (shared)       │
                     │  - ErrorHandler (unified)          │
                     │  - SymbolManager (shared)          │
                     └──────────────────┬────────────────┘
                                        │
         ┌──────────────────────────────┼──────────────────────────────┐
         │                              │                              │
    ┌────▼────────┐              ┌─────▼──────┐              ┌────────▼────┐
    │ Cranelift   │              │    LLVM    │              │ Interpreter │
    │ (specializes│              │(specializes│              │(specializes)│
    │  only what's│              │ only what's│              │             │
    │  different) │              │ different) │              │             │
    └─────────────┘              └────────────┘              └─────────────┘
         │                              │                              │
    Cranelift-                      LLVM IR                     HIR tree-walk
    specific codegen                generation                  interpreter
```

**Benefit**: Shared logic implemented once, backends only implement what's different.

---

## 3. SHARED COMPONENTS DESIGN

### 3.1. Type Mapping System

**Problem**: Each backend reimplements mir_type_to_X() independently.

**Solution**: Create unified TypeMapper trait with shared base implementation.

```simple
# New module: src/compiler/backend/common/type_mapper.spl

trait TypeMapper:
    """
    Maps MIR types to backend-specific type representations.

    Backends implement this trait to provide their specific type system,
    while inheriting common logic for complex types.
    """

    # === Abstract methods (must implement) ===

    fn map_primitive(ty: PrimitiveType) -> text:
        """Map primitive types (i64, f64, bool, etc.)."""
        pass  # Must implement

    fn map_pointer(pointee: text, mutability: Mutability) -> text:
        """Map pointer types."""
        pass  # Must implement

    fn backend_name() -> text:
        """Backend name for error messages."""
        pass  # Must implement

    # === Shared methods (with default implementations) ===

    fn map_type(ty: MirType) -> text:
        """
        Map any MIR type to backend representation.
        Default implementation handles common cases.
        """
        match ty.kind:
            case I64, I32, I16, I8, F64, F32, Bool, Unit:
                self.map_primitive(ty.kind)

            case Ptr(inner, mutability):
                val inner_ty = self.map_type(inner)
                self.map_pointer(inner_ty, mutability)

            case Struct(fields):
                self.map_struct(fields)

            case Array(element, size):
                self.map_array(element, size)

            case Tuple(elements):
                self.map_tuple(elements)

            case Function(params, ret):
                self.map_function(params, ret)

            case _:
                error("Unsupported type in {self.backend_name()}: {ty}")

    fn map_struct(fields: [(text, MirType)]) -> text:
        """
        Map struct type (default implementation).
        Backends can override for custom struct layouts.
        """
        # Default: represent as aggregate of field types
        val field_types = fields.map(\f: self.map_type(f.1))
        "struct {{ {field_types.join(', ')} }}"

    fn map_array(element: MirType, size: i64) -> text:
        """Map array type (default implementation)."""
        val elem_ty = self.map_type(element)
        "[{size} x {elem_ty}]"

    fn map_tuple(elements: [MirType]) -> text:
        """Map tuple type (default implementation)."""
        val elem_types = elements.map(\e: self.map_type(e))
        "{{ {elem_types.join(', ')} }}"

    fn map_function(params: [MirType], ret: MirType) -> text:
        """Map function type (default implementation)."""
        val param_types = params.map(\p: self.map_type(p))
        val ret_type = self.map_type(ret)
        "{ret_type} ({param_types.join(', ')})"

    # === Helper methods ===

    fn size_of(ty: MirType) -> i64:
        """
        Get size in bytes of a type.
        Default implementation uses target-specific info.
        """
        match ty.kind:
            case I64, F64, Ptr(_, _): 8
            case I32, F32: 4
            case I16: 2
            case I8, Bool: 1
            case Unit: 0
            case Struct(fields):
                fields.map(\f: self.size_of(f.1)).sum()
            case Array(elem, size):
                self.size_of(elem) * size
            case _: error("Cannot compute size of {ty}")

    fn align_of(ty: MirType) -> i64:
        """
        Get alignment in bytes of a type.
        Default implementation uses common rules.
        """
        match ty.kind:
            case I64, F64, Ptr(_, _): 8
            case I32, F32: 4
            case I16: 2
            case I8, Bool: 1
            case Struct(fields):
                # Alignment of struct is max alignment of fields
                fields.map(\f: self.align_of(f.1)).max()
            case Array(elem, _):
                self.align_of(elem)
            case _: 1  # Default alignment

# === Backend Implementations ===

class LlvmTypeMapper:
    """LLVM type mapper implementation."""
    target: LlvmTargetConfig

impl TypeMapper for LlvmTypeMapper:
    fn map_primitive(ty: PrimitiveType) -> text:
        match ty:
            case I64: "i64"
            case I32: "i32"
            case I16: "i16"
            case I8: "i8"
            case F64: "double"
            case F32: "float"
            case Bool: "i1"
            case Unit: "void"

    fn map_pointer(pointee: text, mutability: Mutability) -> text:
        # LLVM uses opaque pointers
        "ptr"

    fn backend_name() -> text:
        "LLVM"

class CraneliftTypeMapper:
    """Cranelift type mapper implementation."""
    target: CodegenTarget

impl TypeMapper for CraneliftTypeMapper:
    fn map_primitive(ty: PrimitiveType) -> text:
        match ty:
            case I64: "I64"
            case I32: "I32"
            case I16: "I16"
            case I8: "I8"
            case F64: "F64"
            case F32: "F32"
            case Bool: "I8"  # Cranelift represents bool as i8
            case Unit: "()"  # Empty tuple

    fn map_pointer(pointee: text, mutability: Mutability) -> text:
        # Cranelift pointer type depends on target
        if self.target.is_64bit():
            "I64"  # 64-bit pointer
        else:
            "I32"  # 32-bit pointer

    fn backend_name() -> text:
        "Cranelift"

class WasmTypeMapper:
    """WebAssembly type mapper implementation."""

impl TypeMapper for WasmTypeMapper:
    fn map_primitive(ty: PrimitiveType) -> text:
        match ty:
            case I64: "i64"
            case I32: "i32"
            case I16: "i32"  # Wasm promotes to i32
            case I8: "i32"   # Wasm promotes to i32
            case F64: "f64"
            case F32: "f32"
            case Bool: "i32" # Wasm represents bool as i32
            case Unit: "()"  # No return

    fn map_pointer(pointee: text, mutability: Mutability) -> text:
        "i32"  # WebAssembly uses i32 for memory addresses

    fn backend_name() -> text:
        "WebAssembly"
```

**Benefits**:
- **Eliminates 200+ lines** of duplicated type mapping
- **Consistent behavior** across backends
- **Easy to extend** - new backend implements 2 methods (map_primitive, map_pointer)
- **Testable** - shared logic tested once

---

### 3.2. Literal Evaluation

**Problem**: Every backend duplicates literal conversion logic.

**Solution**: Extract shared LiteralConverter.

```simple
# New module: src/compiler/backend/common/literal_converter.spl

class LiteralConverter:
    """
    Converts HIR literals to backend values.
    Shared across all backends to ensure consistency.
    """

    static fn convert_int(value: i64, ty: MirType?) -> Value:
        """Convert integer literal to value."""
        Value.Int(value)

    static fn convert_float(value: f64, ty: MirType?) -> Value:
        """Convert float literal to value."""
        Value.Float(value)

    static fn convert_string(value: text) -> Value:
        """Convert string literal to value."""
        Value.String(value)

    static fn convert_bool(value: bool) -> Value:
        """Convert boolean literal to value."""
        Value.Bool(value)

    static fn convert_nil() -> Value:
        """Convert nil literal to value."""
        Value.Nil

    static fn convert_array(elements: [Value]) -> Value:
        """Convert array literal to value."""
        Value.Array(elements)

    static fn convert_tuple(elements: [Value]) -> Value:
        """Convert tuple literal to value."""
        Value.Tuple(elements)

    static fn convert_dict(pairs: [(Value, Value)]) -> Value:
        """Convert dict literal to value."""
        val dict: Dict<Value, Value> = {}
        for key, val in pairs:
            dict[key] = val
        Value.Dict(dict)

# === Usage in backends ===

impl InterpreterBackend:
    fn eval_literal(lit: HirExpr) -> Value:
        match lit.kind:
            case IntLit(v, ty):
                LiteralConverter.convert_int(v, ty)
            case StringLit(s, _):
                LiteralConverter.convert_string(s)
            case ArrayLit(elems, _):
                val vals = elems.map(\e: self.eval_expr(e))
                LiteralConverter.convert_array(vals)
            # ... other cases
```

**Benefits**:
- **Eliminates 150+ lines** of duplication
- **Guarantees consistency** - same literal always produces same value
- **Single source of truth** for literal semantics

---

### 3.3. Expression Evaluator Base Class

**Problem**: All backends duplicate expression evaluation structure.

**Solution**: Create abstract ExpressionEvaluator base with common patterns.

```simple
# New module: src/compiler/backend/common/expression_evaluator.spl

abstract class ExpressionEvaluator:
    """
    Base class for expression evaluation.
    Provides common evaluation patterns, backends override specific cases.
    """

    # === Abstract methods (must implement) ===

    me eval_expr_impl(expr: HirExpr, ctx: EvalContext) -> Result<Value, BackendError>:
        """Backend-specific expression evaluation."""
        pass

    # === Template method (shared logic) ===

    me eval_expr(expr: HirExpr, ctx: EvalContext) -> Result<Value, BackendError>:
        """
        Main evaluation entry point.
        Handles common cases, delegates to eval_expr_impl for backend-specific.
        """
        match expr.kind:
            # Literals (shared across all backends)
            case IntLit(v, ty):
                Ok(LiteralConverter.convert_int(v, ty))

            case FloatLit(v, ty):
                Ok(LiteralConverter.convert_float(v, ty))

            case StringLit(s, _):
                Ok(LiteralConverter.convert_string(s))

            case BoolLit(b, _):
                Ok(LiteralConverter.convert_bool(b))

            case NilLit(_):
                Ok(LiteralConverter.convert_nil())

            # Collections (can be shared with small customization)
            case ArrayLit(elems, _):
                self.eval_array_lit(elems, ctx)

            case TupleLit(elems, _):
                self.eval_tuple_lit(elems, ctx)

            case DictLit(pairs, _):
                self.eval_dict_lit(pairs, ctx)

            # Operations (backend-specific, delegate)
            case BinaryOp(op, left, right, _):
                self.eval_binary_op(op, left, right, ctx)

            case UnaryOp(op, operand, _):
                self.eval_unary_op(op, operand, ctx)

            case Call(func, args, _):
                self.eval_call(func, args, ctx)

            # Everything else: delegate to backend
            case _:
                self.eval_expr_impl(expr, ctx)

    # === Helper methods with default implementations ===

    me eval_array_lit(elements: [HirExpr], ctx: EvalContext) -> Result<Value, BackendError>:
        """Evaluate array literal (shared implementation)."""
        var values: [Value] = []
        for elem in elements:
            val v = self.eval_expr(elem, ctx)?
            values = values.push(v)
        Ok(LiteralConverter.convert_array(values))

    me eval_tuple_lit(elements: [HirExpr], ctx: EvalContext) -> Result<Value, BackendError>:
        """Evaluate tuple literal (shared implementation)."""
        var values: [Value] = []
        for elem in elements:
            val v = self.eval_expr(elem, ctx)?
            values = values.push(v)
        Ok(LiteralConverter.convert_tuple(values))

    me eval_dict_lit(pairs: [(HirExpr, HirExpr)], ctx: EvalContext) -> Result<Value, BackendError>:
        """Evaluate dict literal (shared implementation)."""
        var pairs_eval: [(Value, Value)] = []
        for key_expr, val_expr in pairs:
            val key = self.eval_expr(key_expr, ctx)?
            val val = self.eval_expr(val_expr, ctx)?
            pairs_eval = pairs_eval.push((key, val))
        Ok(LiteralConverter.convert_dict(pairs_eval))

    # === Backend-specific methods (can override) ===

    me eval_binary_op(op: BinaryOp, left: HirExpr, right: HirExpr, ctx: EvalContext)
        -> Result<Value, BackendError>:
        """Evaluate binary operation (default: interpreter-style)."""
        val lhs = self.eval_expr(left, ctx)?
        val rhs = self.eval_expr(right, ctx)?

        match op:
            case Add:
                Ok(Value.Int(lhs.as_int() + rhs.as_int()))
            case Sub:
                Ok(Value.Int(lhs.as_int() - rhs.as_int()))
            # ... more ops

    me eval_unary_op(op: UnaryOp, operand: HirExpr, ctx: EvalContext)
        -> Result<Value, BackendError>:
        """Evaluate unary operation (default: interpreter-style)."""
        val val = self.eval_expr(operand, ctx)?

        match op:
            case Neg:
                Ok(Value.Int(-val.as_int()))
            case Not:
                Ok(Value.Bool(not val.as_bool()))

    me eval_call(func: HirExpr, args: [HirExpr], ctx: EvalContext)
        -> Result<Value, BackendError>:
        """Evaluate function call (must override for most backends)."""
        error("Call evaluation not implemented in {self.backend_name()}")

# === Backend Usage ===

class InterpreterBackend extends ExpressionEvaluator:
    """Interpreter inherits common evaluation logic."""

impl InterpreterBackend:
    # Only need to override backend-specific cases
    me eval_expr_impl(expr: HirExpr, ctx: EvalContext) -> Result<Value, BackendError>:
        match expr.kind:
            case VarRef(name, _):
                ctx.env.lookup(name)

            case FieldAccess(obj, field, _):
                val obj_val = self.eval_expr(obj, ctx)?
                obj_val.get_field(field)

            # ... other interpreter-specific cases

    me eval_call(func: HirExpr, args: [HirExpr], ctx: EvalContext)
        -> Result<Value, BackendError>:
        # Interpreter-specific call handling
        val func_val = self.eval_expr(func, ctx)?
        val arg_vals = args.map(\a: self.eval_expr(a, ctx)?)
        func_val.call(arg_vals)
```

**Benefits**:
- **Eliminates 300-400 lines** of duplication per backend
- **Consistent evaluation semantics** (literals, collections always work the same)
- **Easy to customize** - only override what's different
- **Template method pattern** - clear separation of shared vs specialized

---

### 3.4. Error Handling Unification

**Problem**: Two separate error types (BackendError, CodegenError) with overlapping concerns.

**Solution**: Merge into single unified error system.

```simple
# Updated: src/compiler/backend_types.spl

enum BackendError:
    """
    Unified backend error type.
    Replaces separate BackendError and CodegenError.
    """

    # Compilation errors
    CompilationFailed(message: text, span: Span?)
    TypeMismatch(expected: text, got: text, span: Span?)
    UnsupportedFeature(feature: text, backend: text, span: Span?)

    # Runtime errors (interpreter)
    RuntimeError(message: text, span: Span?)
    DivisionByZero(span: Span?)
    NullPointerDereference(span: Span?)
    ArrayIndexOutOfBounds(index: i64, length: i64, span: Span?)

    # Backend-specific errors
    LlvmError(message: text, span: Span?)
    CraneliftError(message: text, span: Span?)
    WasmError(message: text, span: Span?)

    # Permission/access errors
    NotAllowed(operation: text, mode: text, span: Span?)

    # Internal errors
    InternalError(message: text, span: Span?)

impl BackendError:
    fn with_span(span: Span) -> BackendError:
        """Add span to error."""
        match self:
            case CompilationFailed(msg, _):
                BackendError.CompilationFailed(msg, Some(span))
            case TypeMismatch(exp, got, _):
                BackendError.TypeMismatch(exp, got, Some(span))
            # ... other cases

    fn to_diagnostic() -> Diagnostic:
        """Convert to diagnostic for display."""
        match self:
            case CompilationFailed(msg, span):
                Diagnostic(
                    level: DiagnosticLevel.Error,
                    message: "Compilation failed: {msg}",
                    span: span,
                    notes: []
                )
            # ... other cases

    fn is_recoverable() -> bool:
        """Check if error is recoverable."""
        match self:
            case InternalError(_, _): false  # Never recoverable
            case NotAllowed(_, _, _): false  # Permission denied
            case _: true  # Most errors are recoverable

# === Error Context and Recovery ===

class ErrorContext:
    """Tracks error context for better diagnostics."""
    errors: [BackendError]
    warnings: [BackendError]
    current_function: text?
    current_file: text?

impl ErrorContext:
    me add_error(error: BackendError):
        self.errors = self.errors.push(error)

    me add_warning(warning: BackendError):
        self.warnings = self.warnings.push(warning)

    fn has_errors() -> bool:
        self.errors.length > 0

    fn error_count() -> i64:
        self.errors.length

    fn warning_count() -> i64:
        self.warnings.length
```

**Benefits**:
- **Single error type** - no confusion between BackendError and CodegenError
- **Consistent error messages** - same format across backends
- **Better diagnostics** - includes span, context, recovery info
- **Easier error handling** - one type to match on

---

### 3.5. Symbol Management

**Problem**: Symbol management is implicit, each backend handles differently.

**Solution**: Create shared SymbolManager.

```simple
# New module: src/compiler/backend/common/symbol_manager.spl

enum SymbolKind:
    Function
    GlobalVariable
    Constant
    Label
    ExternFunction

struct Symbol:
    name: text
    kind: SymbolKind
    address: i64?
    size: i64
    is_exported: bool
    is_weak: bool

enum RelocKind:
    Absolute     # Direct address
    Relative     # PC-relative
    GotRelative  # GOT-relative

struct Relocation:
    offset: i64         # Offset in section where relocation applies
    symbol: text        # Symbol name to relocate against
    kind: RelocKind
    addend: i64         # Addend for relocation

class SymbolManager:
    """
    Manages symbols and relocations for compiled code.
    Shared across native backends (Cranelift, LLVM).
    """
    symbols: Dict<text, Symbol>
    relocations: [Relocation]
    next_address: i64

    static fn create() -> SymbolManager:
        SymbolManager(
            symbols: {},
            relocations: [],
            next_address: 0
        )

    me register_function(name: text, size: i64, is_exported: bool):
        """Register a function symbol."""
        val address = self.next_address
        self.symbols[name] = Symbol(
            name: name,
            kind: SymbolKind.Function,
            address: Some(address),
            size: size,
            is_exported: is_exported,
            is_weak: false
        )
        self.next_address = self.next_address + size

    me register_global(name: text, size: i64, is_exported: bool):
        """Register a global variable symbol."""
        val address = self.next_address
        self.symbols[name] = Symbol(
            name: name,
            kind: SymbolKind.GlobalVariable,
            address: Some(address),
            size: size,
            is_exported: is_exported,
            is_weak: false
        )
        self.next_address = self.next_address + size

    me register_extern(name: text):
        """Register an external function (FFI)."""
        self.symbols[name] = Symbol(
            name: name,
            kind: SymbolKind.ExternFunction,
            address: nil,  # Resolved at link time
            size: 0,
            is_exported: false,
            is_weak: false
        )

    me add_relocation(offset: i64, symbol: text, kind: RelocKind, addend: i64):
        """Add a relocation entry."""
        self.relocations = self.relocations.push(
            Relocation(offset: offset, symbol: symbol, kind: kind, addend: addend)
        )

    fn get_address(name: text) -> i64?:
        """Get address of a symbol."""
        match self.symbols.get(name):
            case Some(sym): sym.address
            case None: nil

    fn get_symbol(name: text) -> Symbol?:
        """Get symbol by name."""
        self.symbols.get(name)

    fn get_exported_symbols() -> [Symbol]:
        """Get all exported symbols."""
        self.symbols.values().filter(\s: s.is_exported)

    fn get_relocations() -> [Relocation]:
        """Get all relocations."""
        self.relocations
```

**Benefits**:
- **Centralized symbol tracking** - no more scattered symbol management
- **Consistent relocation handling** - same format for all backends
- **Easier linking** - clear interface for linker integration

---

## 4. BACKEND TRAIT REFACTORING

### Current Backend Trait (backend_types.spl)

```simple
# Current: Many methods, all must implement
trait Backend:
    fn process_module(module: HirModule) -> Result<BackendResult, BackendError>
    fn process_function(func: HirFunction) -> Result<BackendResult, BackendError>
    fn process_class(class: HirClass) -> Result<BackendResult, BackendError>
    # ... 10+ more methods
```

**Problem**: Every backend must implement ALL methods, even if they're identical.

### Proposed Backend Trait Hierarchy

```simple
# New design: Trait hierarchy with defaults

trait Backend:
    """
    Main backend interface.
    Backends implement this to provide compilation/interpretation.
    """

    fn backend_name() -> text
    fn supports_target(target: CodegenTarget) -> bool

    fn compile_module(module: MirModule, options: CompileOptions)
        -> Result<BackendResult, BackendError>

# === Specialized backends ===

trait CompilerBackend extends Backend:
    """
    Backend that compiles to native code.
    Provides additional methods for object code generation.
    """

    fn type_mapper() -> TypeMapper
    fn symbol_manager() -> SymbolManager

    fn compile_function(func: MirFunction) -> Result<CompiledFunction, BackendError>
    fn link_module(functions: [CompiledFunction]) -> Result<CompiledModule, BackendError>

trait InterpreterBackend extends Backend:
    """
    Backend that interprets HIR/MIR directly.
    Provides additional methods for runtime evaluation.
    """

    fn eval_expr(expr: HirExpr, ctx: EvalContext) -> Result<Value, BackendError>
    fn eval_stmt(stmt: HirStmt, ctx: EvalContext) -> Result<(), BackendError>

# === Implementations ===

impl CompilerBackend for LlvmBackend:
    fn backend_name() -> text:
        "LLVM"

    fn supports_target(target: CodegenTarget) -> bool:
        # LLVM supports all targets
        true

    fn type_mapper() -> TypeMapper:
        LlvmTypeMapper(target: self.config)

    fn compile_function(func: MirFunction) -> Result<CompiledFunction, BackendError>:
        # LLVM-specific function compilation
        ...

impl CompilerBackend for CraneliftBackend:
    fn backend_name() -> text:
        "Cranelift"

    fn supports_target(target: CodegenTarget) -> bool:
        # Cranelift only supports 64-bit
        target.is_64bit()

    fn type_mapper() -> TypeMapper:
        CraneliftTypeMapper(target: self.target)

    fn compile_function(func: MirFunction) -> Result<CompiledFunction, BackendError>:
        # Cranelift-specific function compilation
        ...

impl InterpreterBackend for TreeWalkInterpreter:
    fn backend_name() -> text:
        "Interpreter"

    fn supports_target(target: CodegenTarget) -> bool:
        # Interpreter doesn't care about target
        true

    fn eval_expr(expr: HirExpr, ctx: EvalContext) -> Result<Value, BackendError>:
        # Use ExpressionEvaluator base class
        ExpressionEvaluator.eval_expr(expr, ctx)
```

**Benefits**:
- **Clear hierarchy** - CompilerBackend vs InterpreterBackend
- **Fewer required methods** - only implement what's relevant
- **Easier to extend** - new backend type? Add new trait variant

---

## 5. BACKEND FACTORY PATTERN

**Problem**: Manual dispatch with match statements scattered throughout code.

**Solution**: Centralized factory with registration.

```simple
# New module: src/compiler/backend/backend_factory.spl

class BackendFactory:
    """
    Factory for creating backends based on target and options.
    Centralizes backend selection logic.
    """

    static fn create(target: CodegenTarget, options: CompileOptions) -> Backend:
        """
        Create appropriate backend for target and options.

        Selection priority:
        1. User override (options.backend_kind)
        2. Target requirements (32-bit → LLVM)
        3. Build mode (debug → Cranelift, release → LLVM)
        4. Default (Cranelift)
        """

        # User override
        if options.backend_kind.?:
            return Self.create_specific(options.backend_kind.unwrap(), target, options)

        # Auto-select based on target and build mode
        val kind = Self.auto_select(target, options.build_mode)
        Self.create_specific(kind, target, options)

    static fn auto_select(target: CodegenTarget, mode: BuildMode) -> BackendKind:
        """Auto-select backend based on target and mode."""

        # 32-bit requires LLVM
        if target.is_32bit():
            return BackendKind.Llvm

        # WebAssembly uses Wasm backend
        if target.is_wasm():
            return BackendKind.Wasm

        # For 64-bit, choose based on build mode
        match mode:
            case BuildMode.Debug:
                BackendKind.Cranelift  # Fast compilation
            case BuildMode.Release:
                BackendKind.Llvm       # Better optimization
            case BuildMode.Test:
                BackendKind.Interpreter  # No compilation overhead
            case BuildMode.Bootstrap:
                BackendKind.Cranelift   # Minimal dependencies

    static fn create_specific(kind: BackendKind, target: CodegenTarget, options: CompileOptions)
        -> Backend:
        """Create specific backend by kind."""

        match kind:
            case BackendKind.Cranelift:
                CraneliftBackend.create(target, options)

            case BackendKind.Llvm:
                LlvmBackend.create(target, options)

            case BackendKind.Wasm:
                WasmBackend.create(target, options)

            case BackendKind.Interpreter:
                TreeWalkInterpreter.create()

            case BackendKind.Lean:
                LeanBackend.create(target, options)

    static fn available_backends() -> [BackendKind]:
        """List all available backends."""
        [
            BackendKind.Cranelift,
            BackendKind.Llvm,
            BackendKind.Wasm,
            BackendKind.Interpreter,
            BackendKind.Lean
        ]

    static fn supports_target(kind: BackendKind, target: CodegenTarget) -> bool:
        """Check if backend supports target."""
        match kind:
            case BackendKind.Cranelift:
                target.is_64bit()  # Cranelift 64-bit only
            case BackendKind.Llvm:
                true  # LLVM supports all targets
            case BackendKind.Wasm:
                target.is_wasm()  # Wasm backend for Wasm targets
            case BackendKind.Interpreter:
                true  # Interpreter supports all
            case BackendKind.Lean:
                true  # Lean backend for all (verification)
```

**Benefits**:
- **Centralized logic** - one place for all backend selection
- **Easy to extend** - register new backend in one place
- **Testable** - backend selection logic is isolated
- **No scattered match statements** - all dispatch in factory

---

## 6. VALUE REPRESENTATION CLEANUP

**Problem**: Mixed interpreter values with FFI pointers in single enum.

**Solution**: Separate value hierarchies.

```simple
# Updated: src/compiler/backend_types.spl

# === Interpreter Values (for tree-walking interpreter) ===

enum InterpreterValue:
    """
    Values used by tree-walking interpreter.
    Pure Simple values, no FFI pointers.
    """
    Nil
    Bool(bool)
    Int(i64)
    Float(f64)
    String(text)
    Array([InterpreterValue])
    Tuple([InterpreterValue])
    Dict(Dict<InterpreterValue, InterpreterValue>)
    Struct(Dict<text, InterpreterValue>)
    Enum(text, [InterpreterValue])  # Variant name + payload
    Function(FunctionRef)
    Closure(FunctionRef, [InterpreterValue])  # Function + captures

impl InterpreterValue:
    fn as_int() -> i64:
        match self:
            case Int(v): v
            case _: error("Expected Int, got {self}")

    fn as_bool() -> bool:
        match self:
            case Bool(b): b
            case _: error("Expected Bool, got {self}")

    # ... other as_* methods

# === Compiled Values (for native backends) ===

enum CompiledValue:
    """
    Values used by compiled code backends (Cranelift, LLVM).
    References to compiled code or RuntimeValue FFI pointers.
    """
    RuntimeValuePtr(ptr: i64)  # Opaque pointer to Rust RuntimeValue
    FunctionPtr(address: i64)  # Native function pointer
    GlobalPtr(address: i64)    # Global variable pointer

# === Backend Result (can be either) ===

enum BackendResult:
    """Result of backend compilation/interpretation."""
    Interpreted(InterpreterValue)      # Interpreter result
    Compiled(CompiledUnit)             # Native code result
    SdnData(SdnValue)                 # SDN export result
    Unit                               # No result
```

**Benefits**:
- **Clear separation** - interpreter values vs compiled values
- **Type safety** - can't mix FFI pointers with interpreter values
- **Better documentation** - each type has clear purpose
- **Safer** - FFI pointers isolated in CompiledValue

---

## 7. MIGRATION PLAN

### Phase 1: Create Shared Components (Week 1)

**Tasks**:
1. ✅ Create `src/compiler/backend/common/` directory
2. ✅ Implement TypeMapper trait and implementations (2 days)
3. ✅ Implement LiteralConverter (1 day)
4. ✅ Implement ExpressionEvaluator base class (2 days)
5. ✅ Write tests for shared components (1 day)

**Deliverable**: Shared components ready for use

### Phase 2: Refactor Error Handling (Week 1)

**Tasks**:
1. ✅ Merge BackendError and CodegenError (1 day)
2. ✅ Update all backends to use unified error type (1 day)
3. ✅ Create ErrorContext class (1 day)
4. ✅ Update tests (1 day)

**Deliverable**: Unified error system

### Phase 3: Refactor Interpreter Backend (Week 2)

**Tasks**:
1. ✅ Migrate interpreter to use TypeMapper (1 day)
2. ✅ Migrate interpreter to use LiteralConverter (1 day)
3. ✅ Migrate interpreter to extend ExpressionEvaluator (2 days)
4. ✅ Remove duplicated code (1 day)
5. ✅ Verify all tests pass (1 day)

**Deliverable**: Refactored interpreter (-300 lines)

### Phase 4: Refactor LLVM Backend (Week 2)

**Tasks**:
1. ✅ Migrate LLVM to use TypeMapper (1 day)
2. ✅ Use LiteralConverter where applicable (1 day)
3. ✅ Remove duplicated type mapping code (1 day)
4. ✅ Verify all tests pass (1 day)

**Deliverable**: Refactored LLVM backend (-200 lines)

### Phase 5: Refactor Cranelift Backend (Week 3)

**Tasks**:
1. ✅ Create CraneliftTypeMapper (1 day)
2. ✅ Migrate Cranelift to use TypeMapper (1 day)
3. ✅ Use shared literal conversion (1 day)
4. ✅ Remove duplicated code (1 day)
5. ✅ Verify all tests pass (1 day)

**Deliverable**: Refactored Cranelift backend (-200 lines)

### Phase 6: Implement Backend Factory (Week 3)

**Tasks**:
1. ✅ Create BackendFactory class (1 day)
2. ✅ Migrate backend selection to factory (1 day)
3. ✅ Remove manual dispatch from backend_api.spl (1 day)
4. ✅ Update CLI to use factory (1 day)
5. ✅ Test factory with all backends (1 day)

**Deliverable**: Centralized backend selection

### Phase 7: Cleanup and Documentation (Week 4)

**Tasks**:
1. ✅ Separate InterpreterValue and CompiledValue (2 days)
2. ✅ Refactor Backend trait hierarchy (2 days)
3. ✅ Write documentation for new architecture (2 days)
4. ✅ Create migration guide (1 day)
5. ✅ Update all examples and tests (1 day)

**Deliverable**: Clean, well-documented architecture

---

## 8. EXPECTED IMPACT

### Code Reduction

| Component | Before | After | Reduction |
|-----------|--------|-------|-----------|
| Type Mapping | 300 lines | 100 lines | -200 lines |
| Literal Conversion | 200 lines | 50 lines | -150 lines |
| Expression Evaluation | 1200 lines | 600 lines | -600 lines |
| Error Handling | 400 lines | 250 lines | -150 lines |
| Backend Selection | 150 lines | 80 lines | -70 lines |
| **Total** | **2250 lines** | **1080 lines** | **-1170 lines (-52%)** |

### Development Time

| Task | Before | After | Improvement |
|------|--------|-------|-------------|
| Add new backend | 800 lines, 3-4 days | 200 lines, 1 day | **75% faster** |
| Fix type mapping bug | 4 places | 1 place | **4x easier** |
| Add new literal type | 4 backends | 1 place | **4x faster** |
| Change error format | 2 types, 10 places | 1 type, 1 place | **10x easier** |

### Testing

| Aspect | Before | After | Improvement |
|--------|--------|-------|-------------|
| Type mapping tests | 4× duplicated | 1× shared | **75% reduction** |
| Literal tests | 4× duplicated | 1× shared | **75% reduction** |
| Error handling tests | Fragmented | Unified | **Consistent** |
| Backend tests | Many integration | Many unit | **Faster** |

---

## 9. RISK ASSESSMENT

### Risk 1: Breaking Changes

**Risk**: Refactoring may break existing code

**Mitigation**:
- Incremental migration (one backend at a time)
- Keep old code until new code proven
- Comprehensive test suite before and after
- Gradual rollout over 4 weeks

**Likelihood**: Medium
**Impact**: Medium
**Overall**: Medium

### Risk 2: Performance Regression

**Risk**: Shared abstractions may be slower than specialized code

**Mitigation**:
- Benchmark before and after
- Inline critical paths
- Profile and optimize hot spots
- Acceptable: 5-10% slowdown for 50% code reduction

**Likelihood**: Low
**Impact**: Low
**Overall**: Low

### Risk 3: Increased Complexity

**Risk**: New abstractions may be harder to understand

**Mitigation**:
- Comprehensive documentation
- Clear examples for each abstraction
- Migration guide for developers
- Code reviews at each phase

**Likelihood**: Low
**Impact**: Medium
**Overall**: Low-Medium

---

## 10. SUCCESS CRITERIA

### Must Have
- ✅ At least 1000 lines of code eliminated
- ✅ All existing tests pass
- ✅ New backend can be added in <1 day
- ✅ Type mapping centralized in one place
- ✅ Error handling unified

### Should Have
- ✅ Performance within 10% of current
- ✅ Comprehensive documentation
- ✅ Migration guide complete
- ✅ No scattered match statements

### Nice to Have
- ⏸️ Performance improvement from optimization
- ⏸️ Automatic backend registration
- ⏸️ Plugin architecture for backends

---

## 11. CONCLUSION

This refactoring design provides:

1. **Significant code reduction**: 1,170+ lines eliminated (52%)
2. **Better maintainability**: Shared logic in one place
3. **Faster development**: New backend in 1 day vs 3-4 days
4. **Cleaner architecture**: Clear separation of concerns
5. **Easier testing**: Shared logic tested once

**Recommendation**: ✅ Approve and begin Phase 1 implementation

**Timeline**: 4 weeks for complete refactoring
**Resource**: 1 engineer half-time (can run in parallel with LLVM implementation)
**Risk**: Low-Medium (incremental migration reduces risk)

---

**Status**: Design Proposal - Ready for Review
**Next Steps**: Approve design → Begin Phase 1
**Target Completion**: 4 weeks from approval
