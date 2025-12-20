# AOP and Dependency Injection Framework for Simple Language

## Overview

This document explores integrating Aspect-Oriented Programming (AOP) and Dependency Injection (DI) into Simple's compilation pipeline, focusing on cross-cutting concerns, the spec test framework, and instrumentation for profiling/coverage.

---

## 1. Cross-Cutting Concerns Analysis

### 1.1 Identified Aspects in Codebase

| Aspect | Current Implementation | Join Points | Advice Type |
|--------|----------------------|--------------|-------------|
| **Logging** | `#[tracing::instrument]` (Rust) | Function entry/exit | Around |
| **Coverage** | `DecisionProbe`, `ConditionProbe` | If/While conditions | Before |
| **Profiling** | `CompileProfiler` phases | Pipeline stages | Around |
| **Contracts** | `ContractCheck` MIR instruction | Function entry/exit | Before/After |
| **Effects** | `Effect::Io`, `Effect::Async` | Capability boundaries | Around |
| **Testing** | BDD hooks (before/after) | Test examples | Before/After |

### 1.2 Cross-Cut Point Categories

```
┌─────────────────────────────────────────────────────────────────────┐
│                        CROSS-CUT TAXONOMY                           │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐             │
│  │  PRIMITIVE  │    │   CUSTOM    │    │   TRAIT     │             │
│  │   TO TYPE   │    │   TYPE      │    │   IMPL      │             │
│  ├─────────────┤    ├─────────────┤    ├─────────────┤             │
│  │ i64 → UserId│    │ @decorator  │    │ impl Trait  │             │
│  │ str → Email │    │ #[attribute]│    │   for Type  │             │
│  │ f64 → Money │    │ class Foo   │    │             │             │
│  └─────────────┘    └─────────────┘    └─────────────┘             │
│        │                  │                  │                      │
│        └──────────────────┼──────────────────┘                      │
│                           │                                         │
│                    ┌──────▼──────┐                                  │
│                    │  JOIN POINT │                                  │
│                    │  MATCHING   │                                  │
│                    └──────┬──────┘                                  │
│                           │                                         │
│         ┌─────────────────┼─────────────────┐                       │
│         │                 │                 │                       │
│  ┌──────▼──────┐   ┌──────▼──────┐   ┌──────▼──────┐               │
│  │   COMPILE   │   │    LINK     │   │   RUNTIME   │               │
│  │   WEAVING   │   │   WEAVING   │   │   WEAVING   │               │
│  ├─────────────┤   ├─────────────┤   ├─────────────┤               │
│  │ MIR probes  │   │ Symbol      │   │ Interpreter │               │
│  │ HIR→MIR     │   │ relocation  │   │ dispatch    │               │
│  │ Type check  │   │ Dead code   │   │ Decorator   │               │
│  └─────────────┘   └─────────────┘   └─────────────┘               │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

## 2. Grammar for Aspect Definitions

### 2.1 Aspect Declaration Syntax

```simple
# Aspect definition
aspect LoggingAspect:
    # Pointcut: pattern matching for join points
    pointcut function_calls:
        call(* *.*(..))                    # All function calls

    pointcut service_methods:
        call(* services.*.*(..))           # Service layer methods

    pointcut io_operations:
        effect(Io | Net | Fs)              # Effect-based matching

    # Advice: code to execute at join points
    before function_calls(ctx: JoinPointContext):
        log.debug("Entering: {ctx.name}")

    after function_calls(ctx: JoinPointContext, result: Any):
        log.debug("Exiting: {ctx.name} -> {result}")

    around io_operations(ctx: JoinPointContext, proceed: Fn() -> Any) -> Any:
        let start = Time.now()
        let result = proceed()
        let elapsed = Time.now() - start
        metrics.record(ctx.name, elapsed)
        return result
```

### 2.2 Pointcut Pattern Language

```bnf
<pointcut>      ::= <pointcut-expr> ('|' <pointcut-expr>)*
<pointcut-expr> ::= <named-pointcut> | <primitive-pointcut> | '(' <pointcut> ')'
<named-pointcut>::= IDENTIFIER

<primitive-pointcut> ::=
    | 'call' '(' <signature-pattern> ')'      # Function/method call
    | 'execution' '(' <signature-pattern> ')' # Function execution
    | 'get' '(' <field-pattern> ')'           # Field read
    | 'set' '(' <field-pattern> ')'           # Field write
    | 'init' '(' <type-pattern> ')'           # Constructor
    | 'effect' '(' <effect-list> ')'          # Effect annotation
    | 'trait' '(' <trait-pattern> ')'         # Trait implementation
    | 'type' '(' <type-pattern> ')'           # Type matching
    | 'attr' '(' <attribute-pattern> ')'      # Attribute matching
    | 'within' '(' <module-pattern> ')'       # Lexical scope

<signature-pattern> ::=
    <return-type-pattern> <type-pattern> '.' <method-pattern> '(' <param-pattern> ')'

<type-pattern>    ::= '*' | IDENTIFIER ('.' IDENTIFIER)* | <type-pattern> '*'
<method-pattern>  ::= '*' | IDENTIFIER | '*' IDENTIFIER | IDENTIFIER '*'
<param-pattern>   ::= '..' | <type-pattern> (',' <type-pattern>)*
<return-type-pattern> ::= '*' | <type-pattern>
<effect-list>     ::= <effect-name> ('|' <effect-name>)*
<effect-name>     ::= 'Io' | 'Net' | 'Fs' | 'Async' | 'Unsafe' | 'Gc'
```

### 2.3 Attribute-Based Aspect Binding

```simple
# Method-level aspect application
@trace                                    # Simple aspect
@cache(ttl: 60.seconds)                   # Parameterized aspect
@retry(max: 3, backoff: exponential)      # Complex configuration
fn fetch_data(url: str) -> Data:
    ...

# Class-level aspect application
@observable                               # All methods observed
@transaction(isolation: ReadCommitted)    # Transaction boundary
class OrderService:
    @inject                               # DI injection point
    repository: OrderRepository

    @logged(level: Debug)                 # Method-specific override
    fn create_order(items: [Item]) -> Order:
        ...

# Module-level aspect application
#[aspect(LoggingAspect)]                  # Apply to all public functions
mod services

# Trait-based aspect (all implementors get aspect)
#[aspected]
trait Repository[T]:
    fn get(id: i64) -> T?
    fn save(item: T) -> bool
```

---

## 3. Weaving: Compile-Time vs Link-Time

### 3.1 Comparison Matrix

| Criterion | Compile-Time (MIR) | Link-Time (Symbol) | Recommendation |
|-----------|-------------------|-------------------|----------------|
| **Granularity** | Expression-level | Function-level | Compile for fine-grained |
| **Performance** | Optimal inlining | Indirect calls | Compile for hot paths |
| **Flexibility** | Fixed at compile | Late binding | Link for plugins |
| **Binary size** | Larger (inlined) | Smaller (shared) | Link for deployment |
| **Debugging** | Source mapping | Symbol resolution | Compile for dev |
| **Coverage** | Decision/Condition | Function entry | Compile for MC/DC |
| **Profiling** | Block-level timing | Call-level timing | Both useful |
| **Logging** | All expressions | Entry/exit only | Compile for verbose |

### 3.2 Decision Tree

```
                        ┌─────────────────┐
                        │ Aspect Required │
                        └────────┬────────┘
                                 │
                    ┌────────────┴────────────┐
                    │                         │
              ┌─────▼─────┐             ┌─────▼─────┐
              │ Expression│             │  Function │
              │  Level?   │             │   Level?  │
              └─────┬─────┘             └─────┬─────┘
                    │                         │
            ┌───────┴───────┐         ┌───────┴───────┐
            │               │         │               │
      ┌─────▼─────┐   ┌─────▼─────┐   │         ┌─────▼─────┐
      │ Coverage  │   │ Contracts │   │         │ Profiling │
      │ MC/DC     │   │ Assertions│   │         │ Timing    │
      └─────┬─────┘   └─────┬─────┘   │         └─────┬─────┘
            │               │         │               │
            └───────┬───────┘         │         ┌─────┴─────┐
                    │                 │         │           │
              ┌─────▼─────┐           │   ┌─────▼─────┐ ┌───▼───┐
              │  COMPILE  │           │   │   LINK    │ │ BOTH  │
              │  WEAVING  │           │   │  WEAVING  │ │       │
              │ (MIR/HIR) │           │   │ (Symbol)  │ │       │
              └───────────┘           │   └───────────┘ └───────┘
                                      │
                              ┌───────┴───────┐
                              │               │
                        ┌─────▼─────┐   ┌─────▼─────┐
                        │  Plugin   │   │ Hot Path  │
                        │ Required? │   │   Perf?   │
                        └─────┬─────┘   └─────┬─────┘
                              │               │
                        ┌─────▼─────┐   ┌─────▼─────┐
                        │   LINK    │   │  COMPILE  │
                        │  WEAVING  │   │  WEAVING  │
                        └───────────┘   └───────────┘
```

### 3.3 Implementation Strategy

#### Compile-Time Weaving (MIR Level)

```rust
// In src/compiler/src/mir/lower.rs
impl MirLowerer {
    fn weave_aspect(&mut self, aspect: &Aspect, stmt: &HirStmt) -> MirLowerResult<()> {
        match aspect.advice_type {
            AdviceType::Before => {
                self.emit_aspect_call(aspect, AdvicePhase::Before)?;
                self.lower_stmt(stmt)?;
            }
            AdviceType::After => {
                self.lower_stmt(stmt)?;
                self.emit_aspect_call(aspect, AdvicePhase::After)?;
            }
            AdviceType::Around => {
                let proceed_label = self.create_proceed_block(stmt)?;
                self.emit_around_advice(aspect, proceed_label)?;
            }
        }
        Ok(())
    }

    fn emit_aspect_call(&mut self, aspect: &Aspect, phase: AdvicePhase) -> MirLowerResult<()> {
        // Generate MIR instructions for aspect invocation
        let ctx_reg = self.build_joinpoint_context()?;
        self.emit_call(aspect.advice_fn, vec![ctx_reg])?;
        Ok(())
    }
}
```

#### Link-Time Weaving (Symbol Level)

```rust
// In src/compiler/src/linker/weaving.rs
pub struct AspectWeaver {
    aspects: Vec<CompiledAspect>,
    symbol_graph: SymbolGraph,
}

impl AspectWeaver {
    pub fn weave(&mut self, settlement: &mut Settlement) -> Result<(), LinkerError> {
        for aspect in &self.aspects {
            let matched_symbols = self.match_pointcut(&aspect.pointcut)?;

            for symbol in matched_symbols {
                match aspect.advice_type {
                    AdviceType::Before => {
                        self.insert_trampoline(symbol, aspect.before_fn)?;
                    }
                    AdviceType::After => {
                        self.wrap_with_after(symbol, aspect.after_fn)?;
                    }
                    AdviceType::Around => {
                        self.replace_with_around(symbol, aspect.around_fn)?;
                    }
                }
            }
        }
        Ok(())
    }

    fn match_pointcut(&self, pointcut: &Pointcut) -> Result<Vec<&str>, LinkerError> {
        self.symbol_graph.symbols
            .iter()
            .filter(|(name, sym)| pointcut.matches(name, sym))
            .map(|(name, _)| *name)
            .collect()
    }
}
```

---

## 4. Integration with Coverage and Profiling

### 4.1 Coverage as Built-in Aspect

```simple
# Coverage aspect (system-provided)
@system
aspect CoverageAspect:
    pointcut decisions:
        within(if | while | match | for)

    pointcut conditions:
        within(and | or | not)

    pointcut paths:
        execution(* *.*(..))

    before decisions(ctx: DecisionContext):
        rt_coverage_decision_probe(ctx.id, ctx.result, ctx.file, ctx.line, ctx.col)

    before conditions(ctx: ConditionContext):
        rt_coverage_condition_probe(ctx.decision_id, ctx.id, ctx.result,
                                     ctx.file, ctx.line, ctx.col)

    after paths(ctx: PathContext):
        rt_coverage_path_finalize(ctx.path_id)
```

### 4.2 Profiling as Built-in Aspect

```simple
# Profiling aspect (system-provided)
@system
aspect ProfilingAspect:
    pointcut all_functions:
        execution(* *.*(..))

    pointcut tagged_functions:
        attr(profile) | attr(benchmark)

    around all_functions(ctx: JoinPointContext, proceed: Fn() -> Any) -> Any:
        let start = rt_profile_start(ctx.name)
        let result = proceed()
        rt_profile_end(start)
        return result
```

### 4.3 Unified Instrumentation Pipeline

```
┌─────────────────────────────────────────────────────────────────────┐
│                    INSTRUMENTATION PIPELINE                         │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Source Code                                                        │
│       │                                                             │
│       ▼                                                             │
│  ┌─────────┐                                                        │
│  │  Parse  │ ──── Extract: decorators, attributes, contracts       │
│  └────┬────┘                                                        │
│       │                                                             │
│       ▼                                                             │
│  ┌─────────┐      ┌──────────────────────────────────┐             │
│  │   HIR   │ ◄────│  Aspect Resolution               │             │
│  └────┬────┘      │  - Match pointcuts to join points│             │
│       │           │  - Resolve aspect priorities     │             │
│       │           └──────────────────────────────────┘             │
│       ▼                                                             │
│  ┌─────────┐      ┌──────────────────────────────────┐             │
│  │   MIR   │ ◄────│  Compile-Time Weaving            │             │
│  └────┬────┘      │  - Insert coverage probes        │             │
│       │           │  - Insert contract checks        │             │
│       │           │  - Inline before/after advice    │             │
│       │           └──────────────────────────────────┘             │
│       ▼                                                             │
│  ┌──────────┐     ┌──────────────────────────────────┐             │
│  │ Cranelift│ ◄───│  Native Code Generation          │             │
│  └────┬─────┘     │  - Emit FFI calls for probes     │             │
│       │           │  - Optimize hot paths            │             │
│       │           └──────────────────────────────────┘             │
│       ▼                                                             │
│  ┌─────────┐      ┌──────────────────────────────────┐             │
│  │  Link   │ ◄────│  Link-Time Weaving               │             │
│  └────┬────┘      │  - Symbol trampolines            │             │
│       │           │  - Dead aspect elimination       │             │
│       │           │  - Cross-module aspects          │             │
│       │           └──────────────────────────────────┘             │
│       ▼                                                             │
│  ┌─────────┐                                                        │
│  │ Runtime │ ──── Runtime counters, profiling hooks, DI container  │
│  └─────────┘                                                        │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

## 5. Dependency Injection Integration

### 5.1 DI Container with AOP Support

```simple
# Service container with aspect support
class DIContainer:
    services: Dict[str, Any]
    aspects: [Aspect]

    fn register[T](name: str, factory: Fn() -> T):
        self.services[name] = factory

    fn resolve[T](name: str) -> T:
        let factory = self.services[name]
        let instance = factory()

        # Apply aspects to resolved service
        for aspect in self.aspects:
            if aspect.matches(T):
                instance = aspect.wrap(instance)

        return instance

    fn register_aspect(aspect: Aspect):
        self.aspects.push(aspect)

# Usage
let container = DIContainer.new()

# Register services
container.register[UserRepository]("user_repo", || SqlUserRepository.new())
container.register[UserService]("user_svc", || {
    let repo = container.resolve[UserRepository]("user_repo")
    UserService.new(repo)
})

# Register aspects
container.register_aspect(LoggingAspect.new())
container.register_aspect(TransactionAspect.new())

# Resolve with aspects applied
let service = container.resolve[UserService]("user_svc")
```

### 5.2 Automatic Injection via Attributes

```simple
class OrderService:
    #[inject]
    repository: OrderRepository

    #[inject(name: "payment_gateway")]
    payment: PaymentGateway

    #[inject(factory: || EmailService.new(Config.smtp))]
    email: EmailService

    fn create_order(items: [Item]) -> Order:
        let order = Order.new(items)
        self.repository.save(order)
        self.payment.charge(order.total)
        self.email.send_confirmation(order)
        return order

# DI container auto-wires injected dependencies
let service = container.create[OrderService]()
```

---

## 6. Spec Test Framework Integration

### 6.1 Test Aspects for Cross-Cutting Concerns

```simple
# Test aspect for database transactions
aspect TestTransactionAspect:
    pointcut test_examples:
        within(it | describe) & attr(transactional)

    around test_examples(ctx: TestContext, proceed: Fn() -> Void):
        let tx = db.begin_transaction()
        try:
            proceed()
            tx.rollback()  # Always rollback for tests
        except e:
            tx.rollback()
            raise e

# Test aspect for mocking
aspect MockingAspect:
    pointcut mock_points:
        call(* *.*(..)) & attr(mock)

    around mock_points(ctx: JoinPointContext, proceed: Fn() -> Any) -> Any:
        if ctx.has_mock():
            return ctx.mock_value()
        return proceed()

# Usage in tests
describe "OrderService":
    #[transactional]           # Aspect applies transaction rollback
    context "creating order":
        #[mock(PaymentGateway, returns: PaymentResult.success())]
        it "processes payment":
            let service = container.resolve[OrderService]()
            let order = service.create_order([item1, item2])
            expect(order.status).to_equal(OrderStatus.Paid)
```

### 6.2 Context Sharing with Aspects

```simple
# Shared context aspect
aspect SharedContextAspect:
    contexts: Dict[str, TestContext]

    pointcut context_blocks:
        execution(context *.*(..))

    before context_blocks(ctx: ContextInfo):
        # Inherit parent context
        if let parent = self.contexts.get(ctx.parent_name):
            ctx.merge(parent)
        self.contexts[ctx.name] = ctx

# Example with shared context
describe "UserService":
    let shared_user = User.new(id: 1, name: "Test")

    context "with existing user":
        before_each:
            repository.save(shared_user)

        it "finds user":
            expect(service.find(1)).to_be_some()

        context "when user is admin":  # Inherits shared_user
            before_each:
                shared_user.role = Role.Admin

            it "has admin privileges":
                expect(shared_user.can_delete()).to_be_true()
```

---

## 7. Primitive to Custom Type Cross-Cutting

### 7.1 Unit Type Aspects

```simple
# Unit type with validation aspect
unit UserId: i64 as uid
    #[aspect(ValidationAspect)]
    invariant:
        self > 0

unit Email: str as email
    #[aspect(ValidationAspect)]
    invariant:
        self.contains("@")
        self.len() <= 255

# Validation aspect for unit types
aspect ValidationAspect:
    pointcut unit_construction:
        init(unit *)

    after unit_construction(ctx: UnitContext):
        if not ctx.value.is_valid():
            raise ValidationError("Invalid {ctx.type_name}: {ctx.value}")
```

### 7.2 Trait-Based Cross-Cutting

```simple
# Loggable trait with automatic aspect
#[aspected(LoggingAspect)]
trait Loggable:
    fn log_id() -> str

# All implementations get logging
impl Loggable for User:
    fn log_id() -> str:
        return "user:{self.id}"

impl Loggable for Order:
    fn log_id() -> str:
        return "order:{self.id}"

# Aspect applies to all Loggable types
aspect LoggingAspect:
    pointcut loggable_methods:
        execution(* Loggable+.*(..))

    before loggable_methods(ctx: JoinPointContext):
        log.info("[{ctx.target.log_id()}] {ctx.method_name}")
```

---

## 8. Configuration and CLI Flags

### 8.1 Compile Options

```rust
pub struct CompileOptions {
    // ... existing fields

    /// Enable AOP weaving
    pub aop_enabled: bool,

    /// Aspect configuration file (aspects.sdn)
    pub aspect_config: Option<PathBuf>,

    /// Weaving mode
    pub weaving_mode: WeavingMode,

    /// Enabled aspect categories
    pub enabled_aspects: Vec<AspectCategory>,
}

#[derive(Debug, Clone, Copy)]
pub enum WeavingMode {
    CompileTime,    // MIR-level weaving
    LinkTime,       // Symbol-level weaving
    Hybrid,         // Both (default)
}

#[derive(Debug, Clone, Copy)]
pub enum AspectCategory {
    Coverage,
    Profiling,
    Logging,
    Contracts,
    Custom,
}
```

### 8.2 CLI Usage

```bash
# Enable all aspects
simple --aop main.spl

# Enable specific aspects
simple --aop=coverage,profiling main.spl

# Configure weaving mode
simple --aop --weaving=compile main.spl    # Compile-time only
simple --aop --weaving=link main.spl       # Link-time only
simple --aop --weaving=hybrid main.spl     # Both (default)

# Use aspect configuration file
simple --aop --aspect-config=aspects.sdn main.spl

# Combined with existing flags
simple --coverage --profile --aop=logging main.spl
```

### 8.3 Aspect Configuration (SDN Format)

```sdn
# aspects.sdn - Aspect configuration

aspects:
    logging:
        enabled: true
        level: Debug
        pointcut: "execution(* services.*.*(..))"
        exclude: ["*.get*", "*.is*"]

    profiling:
        enabled: true
        threshold: 10ms
        pointcut: "execution(* *.*(..)) & !attr(fast)"

    coverage:
        enabled: true
        mode: mcdc
        output: coverage.sdn
        include: ["src/**/*.spl"]
        exclude: ["test/**"]

    transactions:
        enabled: false  # Disabled by default
        pointcut: "execution(* repositories.*.*(..))"
        isolation: ReadCommitted

weaving:
    mode: hybrid
    compile_time:
        - coverage
        - contracts
    link_time:
        - logging
        - profiling

di:
    container: auto
    scan_packages:
        - services
        - repositories
    profiles:
        default:
            - SqlUserRepository as UserRepository
        test:
            - MockUserRepository as UserRepository
```

---

## 9. Implementation Roadmap

### Phase 1: Core Infrastructure (4-6 weeks)
- [ ] Extend MIR with aspect metadata
- [ ] Add pointcut pattern matcher
- [ ] Implement compile-time weaving for coverage/profiling
- [ ] Add `--aop` CLI flags

### Phase 2: Grammar and Parser (3-4 weeks)
- [ ] Add `aspect` keyword and syntax
- [ ] Parse pointcut expressions
- [ ] Add `@inject` and `#[aspect]` attributes
- [ ] Integrate with HIR

### Phase 3: Link-Time Weaving (4-6 weeks)
- [ ] Extend linker with aspect weaver
- [ ] Implement symbol trampolines
- [ ] Add cross-module aspect support
- [ ] Optimize aspect overhead

### Phase 4: DI Integration (3-4 weeks)
- [ ] Build DIContainer runtime
- [ ] Implement auto-wiring
- [ ] Add profile-based configuration
- [ ] Integrate with test framework

### Phase 5: Spec Test Integration (2-3 weeks)
- [ ] Add test aspects (transaction, mocking)
- [ ] Implement context sharing aspects
- [ ] Add aspect-based test fixtures
- [ ] Documentation and examples

---

## 10. Summary

| Feature | Weaving Phase | Cross-Cut Point | Priority |
|---------|--------------|-----------------|----------|
| **Coverage (MC/DC)** | Compile | Decision/Condition | High |
| **Profiling** | Both | Function entry/exit | High |
| **Logging** | Link | Function calls | Medium |
| **Contracts** | Compile | Function boundary | High |
| **DI Injection** | Runtime | Constructor/Field | Medium |
| **Transactions** | Runtime | Method execution | Low |
| **Mocking** | Runtime | Test examples | Medium |
| **Validation** | Compile | Type construction | Low |

The Simple language already has strong foundations for AOP through:
- Decorator/attribute system
- Effect annotations
- Contract checking
- Module boundaries
- Trait implementations

This framework formalizes these patterns into a cohesive AOP model with explicit pointcut language, multiple weaving strategies, and deep integration with coverage, profiling, and dependency injection.
