# Self-Hosting Implementation Plan

## Goal

Migrate Simple compiler from Rust to Simple, with Rust only for:
- Bootstrap parser (temporary)
- Codegen FFI (Cranelift/LLVM bindings)
- Runtime FFI (GC, platform calls)

---

## Phase 1: Infrastructure (P1)

### 1.1 Config System
**File:** `simple/compiler/config.spl`

```simple
class Config:
    profile: text           # dev, test, prod, sdn
    log_level: i64          # 0-10
    settings: Dict<text, text>

    static fn load(path: text) -> Config
    fn merge_env()          # SIMPLE_* env vars
    fn merge_args(args: [text])
    fn get(key: text) -> text?
```

**Tasks:**
- [ ] Create Config class with load/merge
- [ ] Support .sdn config files
- [ ] Environment variable override (SIMPLE_*)
- [ ] Command-line argument override
- [ ] Profile selection (dev, test, prod, sdn)

### 1.2 Dependency Injection
**File:** `simple/compiler/di.spl`

```simple
class DiContainer:
    bindings: Dict<text, fn() -> Any>
    profile: text

    fn bind<T>(trait_name: text, impl: fn() -> T)
    fn resolve<T>(trait_name: text) -> T
    fn with_profile(profile: text) -> DiContainer
```

**Tasks:**
- [ ] Create DiContainer class
- [ ] Profile-based binding selection
- [ ] Lazy instantiation
- [ ] Singleton vs transient scope
- [ ] Bind Backend trait implementations

### 1.3 AOP for Logging
**File:** `simple/compiler/aop.spl`

```simple
class AopWeaver:
    logger: Logger

    fn around(pattern: text, aspect: Aspect)
    fn before(pattern: text, fn: fn())
    fn after(pattern: text, fn: fn())

class LogAspect(Aspect):
    level: i64

    fn apply(fn_name: text, args: [Any], body: fn()) -> Any:
        self.logger.log(self.level, "enter", fn_name)
        val result = body()
        self.logger.log(self.level, "exit", fn_name)
        result
```

**Tasks:**
- [ ] Create AopWeaver class
- [ ] Pattern matching for function names
- [ ] LogAspect implementation
- [ ] Integration with DI container

---

## Phase 2: Parsing Pipeline (P1)

### 2.1 Lexer
**File:** `simple/compiler/lexer.spl`

```simple
enum TokenKind:
    # Literals
    IntLit, FloatLit, StringLit, BoolLit
    # Keywords
    KwFn, KwVal, KwVar, KwIf, KwElse, KwFor, KwWhile
    KwStruct, KwClass, KwEnum, KwTrait, KwImpl
    KwMatch, KwReturn, KwBreak, KwContinue
    # Operators
    Plus, Minus, Star, Slash, Eq, NotEq, Lt, Gt
    # Delimiters
    LParen, RParen, LBrace, RBrace, LBracket, RBracket
    # Punctuation
    Comma, Colon, Semicolon, Dot, Arrow, FatArrow
    # Special
    Newline, Indent, Dedent, Eof, Error

struct Token:
    kind: TokenKind
    span: Span
    value: text

class Lexer:
    source: text
    pos: i64
    line: i64
    col: i64
    indent_stack: [i64]

    fn next_token() -> Token
    fn peek() -> char
    fn advance() -> char
    fn skip_whitespace()
    fn scan_identifier() -> Token
    fn scan_number() -> Token
    fn scan_string() -> Token
```

**Tasks:**
- [ ] Create TokenKind enum (use hir-core BaseTokenKind as reference)
- [ ] Create Token struct with span
- [ ] Implement Lexer class
- [ ] Handle indentation (Indent/Dedent tokens)
- [ ] Handle all operators and delimiters
- [ ] Handle string interpolation
- [ ] Handle comments (# and ##)
- [ ] Write lexer_spec.spl tests

### 2.2 TreeSitter (Outline Parser)
**File:** `simple/compiler/treesitter.spl`

```simple
struct OutlineModule:
    imports: [ImportDecl]
    functions: [FunctionOutline]
    classes: [ClassOutline]
    structs: [StructOutline]
    enums: [EnumOutline]

struct FunctionOutline:
    name: text
    params: [ParamOutline]
    return_type: TypeExpr?
    span: Span
    body_span: Span      # Span of body (for later parsing)

struct ClassOutline:
    name: text
    fields: [FieldOutline]
    methods: [FunctionOutline]
    span: Span

class TreeSitter:
    lexer: Lexer

    fn parse_outline(source: text) -> OutlineModule
    fn parse_imports() -> [ImportDecl]
    fn parse_function_outline() -> FunctionOutline
    fn parse_class_outline() -> ClassOutline
    fn skip_block()        # Skip function body (just track span)
```

**Tasks:**
- [ ] Create outline AST types
- [ ] Implement TreeSitter class
- [ ] Parse top-level declarations only
- [ ] Skip function/method bodies (record spans)
- [ ] Error recovery (continue after errors)
- [ ] Incremental parsing support (for IDE)
- [ ] Write treesitter_spec.spl tests

### 2.3 Parser (Full AST)
**File:** `simple/compiler/parser.spl`

```simple
class Parser:
    lexer: Lexer
    treesitter: TreeSitter
    current: Token
    outline: OutlineModule?

    fn parse(source: text) -> Module:
        # First pass: outline
        self.outline = self.treesitter.parse_outline(source)
        # Second pass: fill in bodies
        self.parse_full()

    fn parse_full() -> Module
    fn parse_function(outline: FunctionOutline) -> Function
    fn parse_expr() -> Expr
    fn parse_stmt() -> Stmt
    fn parse_pattern() -> Pattern
```

**Tasks:**
- [ ] Create full AST types (Expr, Stmt, Pattern, etc.)
- [ ] Implement Parser using TreeSitter outline
- [ ] Parse expressions (binary, unary, call, index, etc.)
- [ ] Parse statements (val, var, if, for, while, match, etc.)
- [ ] Parse patterns (literal, binding, struct, enum, etc.)
- [ ] Parse type expressions
- [ ] Error recovery with synchronization
- [ ] Write parser_spec.spl tests

---

## Phase 3: HIR Layer (P2)

### 3.1 HIR Data Structures
**File:** `simple/compiler/hir.spl`

```simple
struct HirModule:
    name: text
    imports: [HirImport]
    functions: Dict<text, HirFunction>
    structs: Dict<text, HirStruct>
    enums: Dict<text, HirEnum>
    symbols: SymbolTable

struct HirFunction:
    name: text
    params: [HirParam]
    return_type: HirType
    body: [HirStmt]
    span: Span

enum HirExpr:
    Literal(value: HirValue)
    Ident(name: text, resolved: Symbol?)
    Binary(op: BinOp, left: HirExpr, right: HirExpr)
    Unary(op: UnOp, operand: HirExpr)
    Call(callee: HirExpr, args: [HirExpr])
    Index(base: HirExpr, index: HirExpr)
    Field(base: HirExpr, field: text)
    If(cond: HirExpr, then_: [HirStmt], else_: [HirStmt]?)
    Match(scrutinee: HirExpr, arms: [HirMatchArm])
    Lambda(params: [HirParam], body: [HirStmt])
    Block(stmts: [HirStmt])

enum HirStmt:
    Expr(expr: HirExpr)
    Val(name: text, type_: HirType?, init: HirExpr)
    Var(name: text, type_: HirType?, init: HirExpr?)
    Assign(target: HirExpr, value: HirExpr)
    Return(value: HirExpr?)
    Break
    Continue
    For(var_: text, iter: HirExpr, body: [HirStmt])
    While(cond: HirExpr, body: [HirStmt])
```

**Tasks:**
- [ ] Create HirModule, HirFunction, HirStruct, HirEnum
- [ ] Create HirExpr enum with all expression types
- [ ] Create HirStmt enum with all statement types
- [ ] Create HirType for type representation
- [ ] Create SymbolTable for name resolution
- [ ] Create HirValue for literal values
- [ ] AST → HIR lowering
- [ ] Write hir_spec.spl tests

### 3.2 Backend Trait
**File:** `simple/compiler/backend.spl`

```simple
trait Backend:
    fn visit_module(module: HirModule) -> Result<Any, Error>
    fn visit_function(fn_: HirFunction) -> Result<Any, Error>
    fn visit_expr(expr: HirExpr) -> Result<Any, Error>
    fn visit_stmt(stmt: HirStmt) -> Result<Any, Error>

# HIR visits backend
class HirVisitor:
    backend: Backend

    fn visit(module: HirModule) -> Result<Any, Error>:
        self.backend.visit_module(module)
```

**Tasks:**
- [ ] Define Backend trait
- [ ] Create HirVisitor that walks HIR and calls backend
- [ ] DI binding for Backend implementations

---

## Phase 4: Backend Implementations (P2-P3)

### 4.1 Interpreter Backend
**File:** `simple/compiler/interpreter_backend.spl`

```simple
class InterpreterBackend(Backend):
    env: Environment

    fn visit_expr(expr: HirExpr) -> Result<Value, Error>:
        match expr:
            HirExpr.Literal(v) => Ok(v.to_value())
            HirExpr.Binary(op, l, r) =>
                val lv = self.visit_expr(l)?
                val rv = self.visit_expr(r)?
                self.eval_binop(op, lv, rv)
            HirExpr.Call(callee, args) =>
                val fn_ = self.visit_expr(callee)?
                val arg_vals = args.map(\a: self.visit_expr(a)?)
                self.call_function(fn_, arg_vals)
            ...
```

**Tasks:**
- [ ] Implement InterpreterBackend
- [ ] Environment with scopes
- [ ] Evaluate all expression types
- [ ] Execute all statement types
- [ ] Function calls with closures
- [ ] Pattern matching execution
- [ ] Write interpreter_spec.spl tests

### 4.2 Compiler Backend
**File:** `simple/compiler/compiler_backend.spl`

```simple
class CompilerBackend(Backend):
    mir_builder: MirBuilder

    fn visit_expr(expr: HirExpr) -> Result<MirValue, Error>:
        match expr:
            HirExpr.Literal(v) =>
                Ok(self.mir_builder.const_(v))
            HirExpr.Binary(op, l, r) =>
                val lv = self.visit_expr(l)?
                val rv = self.visit_expr(r)?
                Ok(self.mir_builder.binop(op, lv, rv))
            HirExpr.Call(callee, args) =>
                val fn_ = self.visit_expr(callee)?
                val arg_vals = args.map(\a: self.visit_expr(a)?)
                Ok(self.mir_builder.call(fn_, arg_vals))
            ...
```

**Tasks:**
- [ ] Implement CompilerBackend
- [ ] MirBuilder for MIR construction
- [ ] Lower all expressions to MIR
- [ ] Lower all statements to MIR
- [ ] Handle control flow (if, loops, match)
- [ ] Write compiler_backend_spec.spl tests

### 4.3 SDN Backend (No-Op)
**File:** `simple/compiler/sdn_backend.spl`

```simple
class SdnBackend(Backend):
    fn visit_expr(expr: HirExpr) -> Result<SdnValue, Error>:
        match expr:
            HirExpr.Literal(v) =>
                Ok(SdnValue.from_literal(v))
            HirExpr.Call(..) =>
                Err(Error("SDN mode: code execution not allowed"))
            HirExpr.Binary(..) =>
                Err(Error("SDN mode: code execution not allowed"))
            # Only data literals allowed
            _ =>
                Err(Error("SDN mode: only literal data allowed"))
```

**Tasks:**
- [ ] Implement SdnBackend
- [ ] Only allow literal values
- [ ] Block all code execution paths
- [ ] Return SdnValue (data-only)
- [ ] Write sdn_backend_spec.spl tests

---

## Phase 5: MIR and Codegen (P3)

### 5.1 MIR
**File:** `simple/compiler/mir.spl`

```simple
struct MirFunction:
    name: text
    params: [MirType]
    return_type: MirType
    blocks: [MirBlock]

struct MirBlock:
    label: text
    instructions: [MirInst]
    terminator: MirTerminator

enum MirInst:
    Const(dest: MirReg, value: MirValue)
    Copy(dest: MirReg, src: MirReg)
    BinOp(dest: MirReg, op: BinOp, left: MirReg, right: MirReg)
    Call(dest: MirReg?, fn_: MirReg, args: [MirReg])
    Load(dest: MirReg, addr: MirReg)
    Store(addr: MirReg, value: MirReg)
    ...

enum MirTerminator:
    Return(value: MirReg?)
    Jump(target: text)
    Branch(cond: MirReg, then_: text, else_: text)
```

**Tasks:**
- [ ] Create MIR data structures
- [ ] MirBuilder for HIR → MIR lowering
- [ ] Basic block construction
- [ ] SSA form (optional)
- [ ] Write mir_spec.spl tests

### 5.2 Codegen
**File:** `simple/compiler/codegen.spl`

```simple
class Codegen:
    fn generate(mir: MirFunction) -> Result<(), Error>:
        rt_cranelift_begin_function(mir.name)
        for block in mir.blocks:
            rt_cranelift_begin_block(block.label)
            for inst in block.instructions:
                self.emit_inst(inst)
            self.emit_terminator(block.terminator)
        rt_cranelift_end_function()

    fn emit_inst(inst: MirInst):
        match inst:
            MirInst.Const(dest, value) =>
                rt_cranelift_const(dest, value)
            MirInst.BinOp(dest, op, left, right) =>
                rt_cranelift_binop(dest, op, left, right)
            ...
```

**Tasks:**
- [ ] Create Codegen class
- [ ] FFI to Cranelift (rt_cranelift_*)
- [ ] Emit all MIR instructions
- [ ] Handle function calls
- [ ] Handle memory operations
- [ ] Write codegen_spec.spl tests

---

## Phase 6: Bootstrap (P4)

### 6.1 Self-Compile Test
```bash
# Step 1: Compile Simple compiler with Rust compiler
./target/debug/simple build simple/compiler/

# Step 2: Use Simple compiler to compile itself
./simple-compiler simple/compiler/ -o simple-compiler-v2

# Step 3: Use v2 to compile itself
./simple-compiler-v2 simple/compiler/ -o simple-compiler-v3

# Step 4: Verify v2 == v3 (bitwise identical)
diff simple-compiler-v2 simple-compiler-v3
```

**Tasks:**
- [ ] Simple compiler can compile itself
- [ ] Output is bitwise identical across generations
- [ ] Remove Rust compiler from build (keep for bootstrap only)

---

## Timeline

| Phase | Description | Priority | Status |
|-------|-------------|----------|--------|
| 1.1 | Config system | P1 | **Complete** (config.spl with merge_env/merge_args) |
| 1.2 | DI container | P1 | **Complete** (di.spl with Backend trait) |
| 1.3 | AOP logging | P1 | **Complete** (aop.spl with aspects) |
| 1.4 | Compiler init | P1 | **Complete** (simple/compiler/init.spl) |
| 2.1 | Lexer | P1 | **Complete** (lexer.spl - 750+ lines) |
| 2.2 | TreeSitter | P1 | **Complete** (treesitter.spl - 900+ lines) |
| 2.3 | Parser | P1 | **Complete** (parser.spl - 1100+ lines) |
| 3.1 | HIR data | P2 | **Complete** (hir.spl - 1200+ lines) |
| 3.2 | Backend trait | P2 | **Complete** (backend.spl - 900+ lines) |
| 4.1 | Interpreter backend | P2 | **Complete** (InterpreterBackendImpl in backend.spl) |
| 4.2 | Compiler backend | P3 | **Complete** (CompilerBackendImpl uses MirLowering + Codegen) |
| 4.3 | SDN backend | P2 | **Complete** (SdnBackendImpl in backend.spl) |
| 5.1 | MIR | P3 | **Complete** (mir.spl - MIR types, builder, HIR→MIR lowering) |
| 5.2 | Codegen | P3 | **Complete** (codegen.spl - Cranelift FFI, JIT/AOT pipeline) |
| 6.1 | Bootstrap | P4 | **Complete** (driver.spl, main.spl, bootstrap_spec.spl) |

---

## File Structure

```
simple/
├── compiler/
│   ├── mod.spl             # Module exports [DONE]
│   ├── init.spl            # Compiler initialization [DONE]
│   ├── lexer.spl           # Tokenizer [DONE - 750+ lines]
│   ├── treesitter.spl      # Outline parser [DONE - 900+ lines]
│   ├── parser.spl          # Full parser [DONE - 1100+ lines]
│   ├── hir.spl             # HIR types + lowering [DONE - 1200+ lines]
│   ├── backend.spl         # Backend trait + implementations [DONE - 900+ lines]
│   │                       # - InterpreterBackendImpl (complete)
│   │                       # - CompilerBackendImpl (stub)
│   │                       # - SdnBackendImpl (complete)
│   ├── mir.spl             # MIR types + builder [DONE - 1000+ lines]
│   ├── codegen.spl         # Code generation [DONE - 600+ lines]
│   ├── driver.spl          # Compilation driver [DONE - 400+ lines]
│   └── main.spl            # Entry point + CLI [DONE - 350+ lines]
└── std_lib/
    └── src/
        ├── config.spl      # Configuration [DONE - enhanced with merge_env/merge_args]
        ├── di.spl          # DI container + Backend trait [DONE - enhanced]
        ├── aop.spl         # AOP weaver + LogAspects [DONE - new]
        └── test/
            └── unit/
                ├── lexer_spec.spl
                ├── treesitter_spec.spl
                ├── parser_spec.spl
                ├── hir_spec.spl
                ├── interpreter_spec.spl
                ├── compiler_backend_spec.spl
                ├── sdn_backend_spec.spl
                ├── mir_spec.spl
                ├── codegen_spec.spl
                └── bootstrap_spec.spl
```

---

## Success Criteria

1. **Lexer**: Tokenizes all Simple syntax correctly
2. **TreeSitter**: Parses outline in <10ms for 10K lines
3. **Parser**: Parses full AST with good error recovery
4. **HIR**: Shared between all backends
5. **Interpreter**: Passes all existing tests
6. **Compiler**: Generates correct native code
7. **SDN**: Blocks all code execution
8. **Bootstrap**: Compiler compiles itself identically
