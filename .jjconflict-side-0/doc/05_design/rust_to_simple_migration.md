# Rust to Simple Migration Plan

## Principle

**Simple code MUST be shorter than Rust equivalent.**

Transfer logic to Simple when:
1. Business logic (not performance critical)
2. Configuration and setup
3. CLI and user interface
4. Report generation
5. Data transformation

Keep in Rust when:
1. Performance critical (parser, codegen)
2. Low-level memory management
3. FFI bindings
4. Unsafe operations

---

## Migration Categories

### Category A: Full Migration (Rust → Simple)

These modules can be fully rewritten in Simple:

| Module | Rust Lines | Simple Target | Ratio |
|--------|------------|---------------|-------|
| CLI apps | 9,044 | 5,216 (done) | 58% |
| Config loading | ~500 | ~150 | 30% |
| Report generation | ~1,500 | ~400 | 27% |
| DB query logic | ~800 | ~200 | 25% |
| Log formatting | ~300 | ~100 | 33% |

### Category B: Partial Migration (Logic in Simple, Core in Rust)

These modules split between Simple (logic) and Rust (FFI):

| Module | Rust FFI | Simple Logic | Total |
|--------|----------|--------------|-------|
| SDN | 274 (ffi) | 133 (cli) | 407 |
| Time | 666 (ffi) | 130 (wrapper) | 796 |
| DB | ~200 (ffi) | 251 (logic) | 451 |
| Log | ~100 (ffi) | 143 (logic) | 243 |

### Category C: Stay in Rust (FFI only)

These stay in Rust, exposed via FFI:

| Module | Lines | Reason |
|--------|-------|--------|
| Parser | 20,000 | Performance |
| Compiler | 30,000 | Performance |
| Runtime | 15,000 | Memory management |
| GC | 2,000 | Unsafe operations |
| Codegen | 5,000 | Low-level |

---

## Transfer Strategy

### Step 1: Identify Transferable Logic

```
Rust Module
    │
    ├── Core Logic (keep in Rust as FFI)
    │   - Parsing
    │   - Memory allocation
    │   - Unsafe operations
    │
    └── High-Level Logic (transfer to Simple)
        - Configuration
        - Orchestration
        - Formatting
        - User interaction
```

### Step 2: Create FFI Interface

```rust
// Rust: Minimal FFI functions
#[no_mangle]
pub extern "C" fn rt_module_core_op(arg: i64) -> i64 {
    // Core logic stays here
}
```

```simple
# Simple: High-level logic
extern fn rt_module_core_op(arg: i64) -> i64

fn do_complex_task(input: text) -> Result<Output>:
    # Orchestration in Simple
    val parsed = parse(input)
    val processed = rt_module_core_op(parsed.value)
    format_output(processed)
```

### Step 3: Migrate Tests

```
Rust Tests → Simple Specs

test_module.rs (50 tests)
    ↓
module_spec.spl (50 specs, shorter syntax)
```

---

## Concrete Migration Plan

### Phase 1: Configuration System (Week 1)

**Goal**: Move all config handling to Simple

#### 1.1 Create config.spl

```simple
# simple/std_lib/src/config.spl

struct LogConfig:
    global_level: i64
    scopes: Dict<text, i64>
    timestamps: bool
    format: text

struct DiConfig:
    profile: text
    bindings: Dict<text, text>

struct AppConfig:
    log: LogConfig
    di: DiConfig
    mode: text

fn load_config(path: text) -> AppConfig:
    val content = rt_file_read(path)
    val sdn = parse_sdn(content)
    AppConfig(
        log: parse_log_config(sdn["log"]),
        di: parse_di_config(sdn["di"]),
        mode: sdn["mode"] ?? "interpret"
    )

fn parse_log_config(data: SdnValue) -> LogConfig:
    LogConfig(
        global_level: data["global_level"] as i64 ?? 4,
        scopes: parse_scopes(data["scopes"]),
        timestamps: data["timestamps"] as bool ?? true,
        format: data["format"] as text ?? "text"
    )
```

**Rust FFI needed**:
```rust
extern fn rt_file_read(path: text) -> text
extern fn rt_sdn_parse(content: text) -> SdnValue  // Already exists
```

**Size comparison**:
- Rust config loading: ~500 lines
- Simple config.spl: ~150 lines
- Reduction: 70%

#### 1.2 Create di.spl

```simple
# simple/std_lib/src/di.spl

struct Container:
    profile: text
    bindings: Dict<text, fn() -> Any>

impl Container:
    static fn with_profile(profile: text) -> Container:
        var bindings: Dict<text, fn() -> Any> = {}

        match profile:
            case "test":
                bindings["InstructionModule"] = \: MockInstructionModule()
                bindings["LogConfig"] = \: LogConfig.testing()
            case "dev":
                bindings["InstructionModule"] = \: FullInstructionModule()
                bindings["LogConfig"] = \: LogConfig.development()
            case "prod":
                bindings["InstructionModule"] = \: OptInstructionModule()
                bindings["LogConfig"] = \: LogConfig.production()
            case "sdn":
                bindings["InstructionModule"] = \: NoOpInstructionModule()
                bindings["LogConfig"] = \: LogConfig.sdn()

        Container(profile: profile, bindings: bindings)

    fn resolve<T>(name: text) -> T:
        val factory = self.bindings[name]
        factory() as T
```

**Size comparison**:
- Rust DI: ~400 lines
- Simple di.spl: ~80 lines
- Reduction: 80%

---

### Phase 2: Instruction Modules (Week 2)

**Goal**: Define instruction behavior in Simple, execute via FFI

#### 2.1 Instruction Types in Simple

```simple
# simple/std_lib/src/instruction.spl

enum HirInstruction:
    LoadConst(value: Value)
    LoadLocal(slot: i64)
    StoreLocal(slot: i64)
    BinOp(op: BinOpKind, left: HirInstruction, right: HirInstruction)
    Call(func: text, args: [HirInstruction])
    MethodCall(receiver: HirInstruction, method: text, args: [HirInstruction])
    FieldGet(object: HirInstruction, field: text)
    FieldSet(object: HirInstruction, field: text, value: HirInstruction)
    Branch(cond: HirInstruction, then_block: [HirInstruction], else_block: [HirInstruction])
    Return(value: HirInstruction?)
    ArrayNew(elements: [HirInstruction])
    DictNew(pairs: [(HirInstruction, HirInstruction)])

trait InstructionModule:
    fn execute(inst: HirInstruction, ctx: ExecutionContext) -> Result<Value>
    fn is_allowed(inst: HirInstruction) -> bool
```

#### 2.2 NoOp Module for SDN

```simple
# simple/std_lib/src/instruction/noop.spl

struct NoOpInstructionModule

impl NoOpInstructionModule: InstructionModule:
    fn execute(inst: HirInstruction, ctx: ExecutionContext) -> Result<Value>:
        match inst:
            case LoadConst(value):
                Ok(value)
            case ArrayNew(elements):
                Ok(Value.Array(elements.map(\e: self.execute(e, ctx).unwrap())))
            case DictNew(pairs):
                Ok(Value.Dict(pairs.map(\p: (self.execute(p.0, ctx).unwrap(), self.execute(p.1, ctx).unwrap()))))
            case _:
                Err(Error("Code execution not allowed in SDN mode"))

    fn is_allowed(inst: HirInstruction) -> bool:
        match inst:
            case LoadConst(_) | ArrayNew(_) | DictNew(_):
                true
            case _:
                false
```

**Size comparison**:
- Rust InstructionModule: ~600 lines
- Simple instruction modules: ~200 lines
- Reduction: 67%

---

### Phase 3: AOP in Simple (Week 3)

**Goal**: Define aspects and weaving in Simple

#### 3.1 Pointcut and Advice

```simple
# simple/std_lib/src/aop.spl

enum Pointcut:
    Instruction(kind: InstructionKind)
    Call(function: text)
    Scope(scope: text)
    LogLevel(min_level: i64)
    And(left: Pointcut, right: Pointcut)
    Or(left: Pointcut, right: Pointcut)
    Not(inner: Pointcut)

enum Advice:
    LogBefore(level: i64, message: text)
    LogAfter(level: i64, message: text)
    LogError(level: i64)
    TimeExecution(scope: text)

struct Aspect:
    name: text
    pointcut: Pointcut
    advice: [Advice]
    enabled: bool

struct AopConfig:
    aspects: [Aspect]
    enabled: bool

impl AopConfig:
    static fn with_logging() -> AopConfig:
        AopConfig(
            aspects: [
                Aspect(
                    name: "call_logging",
                    pointcut: Pointcut.Instruction(InstructionKind.Call),
                    advice: [
                        Advice.LogBefore(5, "Calling {function}"),
                        Advice.LogAfter(5, "Returned from {function}")
                    ],
                    enabled: true
                ),
                Aspect(
                    name: "error_logging",
                    pointcut: Pointcut.LogLevel(2),
                    advice: [Advice.LogError(2)],
                    enabled: true
                )
            ],
            enabled: true
        )
```

#### 3.2 Weaver

```simple
# simple/std_lib/src/aop/weaver.spl

struct Weaver:
    config: AopConfig
    log_config: LogConfig

impl Weaver:
    fn execute_with_aspects(
        inst: HirInstruction,
        module: InstructionModule,
        ctx: ExecutionContext
    ) -> Result<Value>:
        if not self.config.enabled:
            return module.execute(inst, ctx)

        val matching_aspects = self.config.aspects
            .filter(\a: a.enabled and self.matches(a.pointcut, inst))

        # Before advice
        for aspect in matching_aspects:
            for advice in aspect.advice:
                self.execute_before(advice, inst, ctx)

        # Execute
        val result = module.execute(inst, ctx)

        # After advice
        for aspect in matching_aspects:
            for advice in aspect.advice:
                self.execute_after(advice, inst, result, ctx)

        result

    fn matches(pointcut: Pointcut, inst: HirInstruction) -> bool:
        match pointcut:
            case Instruction(kind):
                inst.kind() == kind
            case Call(function):
                match inst:
                    case Call(func, _): func == function or function == "*"
                    case _: false
            case And(left, right):
                self.matches(left, inst) and self.matches(right, inst)
            case Or(left, right):
                self.matches(left, inst) or self.matches(right, inst)
            case Not(inner):
                not self.matches(inner, inst)
            case _:
                false
```

**Size comparison**:
- Rust AOP: ~800 lines
- Simple aop.spl: ~150 lines
- Reduction: 81%

---

### Phase 4: Parser Outline Mode (Week 4)

**Goal**: Outline parsing logic in Simple, tokenization in Rust

#### 4.1 Outline Types

```simple
# simple/std_lib/src/parse/outline.spl

struct OutlineModule:
    path: text
    imports: [OutlineImport]
    types: [OutlineType]
    functions: [OutlineFunction]
    exports: [text]

struct OutlineFunction:
    name: text
    params: [(text, text?)]  # (name, type)
    return_type: text?
    is_async: bool
    is_pub: bool
    span: Span

struct OutlineType:
    kind: TypeKind
    name: text
    generics: [text]
    fields: [(text, text)]
    is_pub: bool
    span: Span

enum TypeKind:
    Struct
    Class
    Enum
    Trait
```

#### 4.2 Outline Parser

```simple
# simple/std_lib/src/parse/outline_parser.spl

extern fn rt_tokenize(source: text) -> [Token]

struct OutlineParser:
    tokens: [Token]
    pos: i64

impl OutlineParser:
    static fn parse(source: text) -> Result<OutlineModule>:
        val tokens = rt_tokenize(source)
        var parser = OutlineParser(tokens: tokens, pos: 0)
        parser.parse_module()

    fn parse_module() -> Result<OutlineModule>:
        var imports: [OutlineImport] = []
        var types: [OutlineType] = []
        var functions: [OutlineFunction] = []
        var exports: [text] = []

        while not self.is_at_end():
            self.skip_whitespace()

            match self.peek().kind:
                case TokenKind.KwImport:
                    imports.push(self.parse_import()?)
                case TokenKind.KwStruct | TokenKind.KwClass | TokenKind.KwEnum:
                    types.push(self.parse_type_decl()?)
                case TokenKind.KwFn:
                    functions.push(self.parse_function_sig()?)
                case TokenKind.KwExport:
                    exports.extend(self.parse_exports()?)
                case _:
                    self.advance()  # Skip unknown

        Ok(OutlineModule(
            path: "",
            imports: imports,
            types: types,
            functions: functions,
            exports: exports
        ))

    fn parse_function_sig() -> Result<OutlineFunction>:
        val start = self.pos
        self.expect(TokenKind.KwFn)?
        val name = self.expect_ident()?
        self.expect(TokenKind.LParen)?
        val params = self.parse_params()?
        self.expect(TokenKind.RParen)?

        var return_type: text? = None
        if self.check(TokenKind.Arrow):
            self.advance()
            return_type = Some(self.parse_type()?)

        # Skip body - just find the end
        self.skip_to_next_declaration()

        Ok(OutlineFunction(
            name: name,
            params: params,
            return_type: return_type,
            is_async: false,
            is_pub: false,
            span: Span(start, self.pos)
        ))
```

**Size comparison**:
- Rust outline parser: Would be ~1000 lines
- Simple outline_parser.spl: ~200 lines
- Reduction: 80%

**Note**: Tokenization stays in Rust (performance critical)

---

### Phase 5: Report Generation (Week 5)

**Goal**: All report generation in Simple

#### 5.1 Markdown Reports

```simple
# simple/std_lib/src/report/markdown.spl

fn generate_table(headers: [text], rows: [[text]]) -> text:
    var md = "| {headers.join(\" | \")} |\n"
    md = md + "|{headers.map(\\_: \"---\").join(\"|\")}|\n"
    for row in rows:
        md = md + "| {row.join(\" | \")} |\n"
    md

fn generate_todo_report(todos: TodoTable) -> text:
    var md = "# TODO Report\n\n"

    # Summary
    md = md + "## Summary\n\n"
    md = md + "- Open: {todos.count_by_status(\"open\")}\n"
    md = md + "- Closed: {todos.count_by_status(\"closed\")}\n\n"

    # By Priority
    md = md + "## By Priority\n\n"
    for priority in ["P0", "P1", "P2", "P3"]:
        val count = todos.count_by_priority(priority)
        if count > 0:
            md = md + "### {priority} ({count})\n\n"
            md = md + generate_table(
                ["ID", "Description", "File"],
                todos.by_priority(priority).map(\t: [t.id, t.description, t.file])
            )
            md = md + "\n"

    md

fn generate_feature_report(features: FeatureTable) -> text:
    var md = "# Feature Report\n\n"

    val by_status = features.table.group_by("status")

    for status in ["done", "in_progress", "planned"]:
        if status in by_status:
            val items = by_status[status]
            md = md + "## {status.capitalize()} ({items.len()})\n\n"
            md = md + generate_table(
                ["Name", "Category", "Description"],
                items.map(\f: [f[1], f[2], f[4]])
            )
            md = md + "\n"

    md
```

**Size comparison**:
- Rust report generation: ~1500 lines (scattered)
- Simple report.spl: ~100 lines
- Reduction: 93%

---

## Migration Summary

### Total Lines

| Category | Rust Before | After (Rust FFI) | After (Simple) | Reduction |
|----------|-------------|------------------|----------------|-----------|
| Config | 500 | 50 | 150 | 60% |
| DI | 400 | 0 | 80 | 80% |
| Instructions | 600 | 100 | 200 | 50% |
| AOP | 800 | 50 | 150 | 75% |
| Outline Parser | 1000 | 200 | 200 | 60% |
| Reports | 1500 | 0 | 100 | 93% |
| CLI Apps | 9044 | 2000 | 5216 | 20% |
| **Total** | **13,844** | **2,400** | **6,096** | **39%** |

### What Stays in Rust (FFI)

```
Core FFI (~2,400 lines):
├── rt_tokenize()      - Tokenization
├── rt_file_read()     - File I/O
├── rt_file_write()    - File I/O
├── rt_sdn_parse()     - SDN parsing
├── rt_execute_mir()   - MIR execution (JIT)
├── rt_gc_collect()    - GC operations
└── rt_alloc/dealloc() - Memory
```

### What Moves to Simple

```
Simple Logic (~6,096 lines):
├── config.spl         - Configuration loading
├── di.spl             - Dependency injection
├── instruction/*.spl  - Instruction definitions
├── aop.spl            - Aspect definitions
├── parse/outline.spl  - Outline parsing
├── report/*.spl       - Report generation
├── db.spl             - Database operations
├── log.spl            - Logging
└── app/*.spl          - CLI applications
```

---

## Implementation Order

```
Week 1: config.spl + di.spl
        ↓
Week 2: instruction/*.spl
        ↓
Week 3: aop.spl + weaver.spl
        ↓
Week 4: parse/outline.spl
        ↓
Week 5: report/*.spl
        ↓
Week 6: Migrate tests (Rust → Simple specs)
```

### Success Metrics

1. **Size**: Simple code < 50% of Rust equivalent
2. **Tests**: All existing tests pass (as Simple specs)
3. **Performance**: No regression > 10%
4. **Coverage**: Same functionality

---

## Test Migration Pattern

### Rust Test → Simple Spec

```rust
// Rust: src/rust/driver/tests/config_tests.rs
#[test]
fn test_load_config() {
    let config = load_config("test.sdn").unwrap();
    assert_eq!(config.log.global_level, 5);
    assert_eq!(config.di.profile, "dev");
}

#[test]
fn test_config_defaults() {
    let config = AppConfig::default();
    assert_eq!(config.log.global_level, 4);
}
```

```simple
# Simple: simple/std_lib/test/unit/config_spec.spl

describe "load_config":
    it "loads config from SDN file":
        val config = load_config("test.sdn")
        expect config.log.global_level == 5
        expect config.di.profile == "dev"

describe "AppConfig":
    it "has sensible defaults":
        val config = AppConfig.default()
        expect config.log.global_level == 4
```

**Size comparison**:
- Rust test: 15 lines
- Simple spec: 10 lines
- Reduction: 33%
