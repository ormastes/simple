# Unified Architecture - Detailed Design

## Overview

This document details the architecture for sharing logic between compiler, interpreter, SDN, and TreeSitter with:
- **Dependency Injection (DI)** for module configuration
- **AOP** for logging and cross-cutting concerns
- **10-level logging** with configurable severity
- **Two-layer parser** (outline/full)
- **Shared instruction model** between interpreter and compiler

---

## Architecture Layers

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         CONFIGURATION LAYER                                  │
│  ┌───────────────┐ ┌───────────────┐ ┌───────────────┐ ┌─────────────────┐  │
│  │  LogConfig    │ │  DiConfig     │ │  AopConfig    │ │  ModeConfig     │  │
│  │  levels 0-10  │ │  profiles     │ │  advice       │ │  interpret/jit  │  │
│  │  scopes       │ │  bindings     │ │  pointcuts    │ │  aot            │  │
│  └───────────────┘ └───────────────┘ └───────────────┘ └─────────────────┘  │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                      DEPENDENCY INJECTION CONTAINER                          │
│  ┌─────────────────────────────────────────────────────────────────────────┐│
│  │  ServiceContainer                                                        ││
│  │  ├── profile: test | dev | prod | sdn                                   ││
│  │  ├── bindings: Map<TypeId, Factory>                                     ││
│  │  └── resolve<T>() -> T                                                  ││
│  └─────────────────────────────────────────────────────────────────────────┘│
│                                                                              │
│  Profiles:                                                                   │
│  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐                        │
│  │   test   │ │   dev    │ │   prod   │ │   sdn    │                        │
│  │ MockInst │ │ FullInst │ │ OptInst  │ │ NoOpInst │                        │
│  │ LogAll   │ │ LogDebug │ │ LogWarn  │ │ LogError │                        │
│  └──────────┘ └──────────┘ └──────────┘ └──────────┘                        │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                         PARSER LAYER (Two-Part)                              │
│                                                                              │
│  ┌─────────────────────────────────┐  ┌─────────────────────────────────┐   │
│  │     HIGH-LEVEL (Outline)        │  │      LOW-LEVEL (Full)           │   │
│  │  ┌───────────────────────────┐  │  │  ┌───────────────────────────┐  │   │
│  │  │ TreeSitter Compatible     │  │  │  │ Type Resolution           │  │   │
│  │  │ - Declarations only       │  │  │  │ - Full type inference     │  │   │
│  │  │ - No function bodies      │  │  │  │ - Generic instantiation   │  │   │
│  │  │ - Quick parsing           │  │  │  │ - Trait resolution        │  │   │
│  │  │ - Error recovery          │  │  │  └───────────────────────────┘  │   │
│  │  │ - Syntax highlighting     │  │  │  ┌───────────────────────────┐  │   │
│  │  └───────────────────────────┘  │  │  │ Macro Expansion           │  │   │
│  │                                 │  │  │ - Hygiene                 │  │   │
│  │  Output: OutlineModule          │  │  │ - Quote/unquote           │  │   │
│  │  - struct/class declarations    │  │  └───────────────────────────┘  │   │
│  │  - function signatures          │  │  ┌───────────────────────────┐  │   │
│  │  - import/export                │  │  │ Effect Inference          │  │   │
│  │  - spans for each item          │  │  │ - IO, Async, Pure         │  │   │
│  │                                 │  │  │ - Effect polymorphism     │  │   │
│  └─────────────────────────────────┘  │  └───────────────────────────┘  │   │
│                                       │                                  │   │
│                                       │  Output: FullModule              │   │
│                                       │  - Complete AST                  │   │
│                                       │  - Type annotations              │   │
│                                       │  - Effect annotations            │   │
│                                       └─────────────────────────────────┘   │
│                                                                              │
│  SDN Parser (Data Only - Injected NoOp Instructions):                        │
│  ┌─────────────────────────────────────────────────────────────────────────┐│
│  │  Uses DI profile "sdn" → InstructionModule = NoOpInstructionModule      ││
│  │  - Parsing allowed                                                       ││
│  │  - Code execution blocked (NoOp for all instructions)                    ││
│  │  - Only data literals evaluated                                          ││
│  └─────────────────────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                    SHARED INSTRUCTION LAYER (simple-hir-core)                │
│                                                                              │
│  ┌─────────────────────────────────────────────────────────────────────────┐│
│  │                     HIGH-LEVEL INSTRUCTIONS (HIR)                        ││
│  │  ┌─────────────────┐ ┌─────────────────┐ ┌─────────────────────────────┐││
│  │  │ Data Operations │ │ Control Flow    │ │ Object Operations           │││
│  │  │ - LoadConst     │ │ - Branch        │ │ - FieldGet                  │││
│  │  │ - LoadLocal     │ │ - Jump          │ │ - FieldSet                  │││
│  │  │ - StoreLocal    │ │ - Call          │ │ - MethodCall                │││
│  │  │ - BinOp         │ │ - Return        │ │ - Construct                 │││
│  │  │ - UnaryOp       │ │ - Match         │ │ - ArrayNew                  │││
│  │  └─────────────────┘ └─────────────────┘ └─────────────────────────────┘││
│  │  ┌─────────────────┐ ┌─────────────────┐ ┌─────────────────────────────┐││
│  │  │ Constraints     │ │ Effects         │ │ Memory                      │││
│  │  │ - TypeAssert    │ │ - EffectBoundary│ │ - Alloc                     │││
│  │  │ - CapabilityChk │ │ - EffectMark    │ │ - Dealloc                   │││
│  │  │ - Precondition  │ │ - Suspend       │ │ - RefCount                  │││
│  │  │ - Postcondition │ │ - Resume        │ │ - GcSafepoint               │││
│  │  │ - Invariant     │ │                 │ │                             │││
│  │  └─────────────────┘ └─────────────────┘ └─────────────────────────────┘││
│  └─────────────────────────────────────────────────────────────────────────┘│
│                                                                              │
│  ┌─────────────────────────────────────────────────────────────────────────┐│
│  │                          DATA LAYOUT                                     ││
│  │  ┌─────────────────┐ ┌─────────────────┐ ┌─────────────────────────────┐││
│  │  │ StructLayout    │ │ EnumLayout      │ │ UnionLayout                 │││
│  │  │ - fields[]      │ │ - tag_size      │ │ - variants[]                │││
│  │  │ - size          │ │ - variants[]    │ │ - max_size                  │││
│  │  │ - align         │ │ - discriminant  │ │ - align                     │││
│  │  └─────────────────┘ └─────────────────┘ └─────────────────────────────┘││
│  └─────────────────────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────────────────────┘
                          │                             │
            ┌─────────────┘                             └─────────────┐
            ▼                                                         ▼
┌───────────────────────────────────┐         ┌───────────────────────────────┐
│      INTERPRETER BACKEND          │         │      COMPILER BACKEND         │
│  ┌─────────────────────────────┐  │         │  ┌─────────────────────────┐  │
│  │ TreeWalkingExecutor         │  │         │  │ MIR Lowering            │  │
│  │ - Executes HIR directly     │  │         │  │ - HIR → MIR (80+ inst)  │  │
│  │ - Value enum (AST refs)     │  │         │  │ - Register allocation   │  │
│  │ - Immediate feedback        │  │         │  │ - Optimization passes   │  │
│  └─────────────────────────────┘  │         │  └─────────────────────────┘  │
│  ┌─────────────────────────────┐  │         │  ┌─────────────────────────┐  │
│  │ Environment                 │  │         │  │ Code Generation         │  │
│  │ - Scope stack               │  │         │  │ - Cranelift / LLVM      │  │
│  │ - Variable bindings         │  │         │  │ - RuntimeValue          │  │
│  │ - Closure capture           │  │         │  │ - NaN-boxing            │  │
│  └─────────────────────────────┘  │         │  └─────────────────────────┘  │
└───────────────────────────────────┘         └───────────────────────────────┘
                          │                             │
                          └─────────────┬───────────────┘
                                        ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                           FFI BRIDGE                                         │
│  ┌─────────────────────────────────────────────────────────────────────────┐│
│  │  BridgeValue: Type-safe conversion between Value ↔ RuntimeValue         ││
│  │  - Interpreter Value → FFI → RuntimeValue                               ││
│  │  - RuntimeValue → FFI → Interpreter Value                               ││
│  │  - Callbacks: Rust calling Simple                                       ││
│  │  - Upcalls: Simple calling Rust                                         ││
│  └─────────────────────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Log Level System (0-10)

### Level Definitions

| Level | Name | Use Case | Default Action |
|-------|------|----------|----------------|
| 0 | Off | No logging | - |
| 1 | Fatal | Unrecoverable, panic | Always show, abort |
| 2 | Error | Recoverable errors | Always show |
| 3 | Warn | Potential issues | Show in prod |
| 4 | Info | High-level events | Show in dev |
| 5 | Debug | Detailed events | Show in debug |
| 6 | Trace | Token/alloc level | Verbose mode |
| 7 | Verbose | Every instruction | Trace mode |
| 8 | Hyper | Memory operations | Special debug |
| 9 | Ultra | GC internals | GC debug |
| 10 | All | Everything | Full trace |

### Configuration Structure

```rust
// src/rust/hir-core/src/config.rs

/// Log configuration with 10 levels
#[derive(Debug, Clone)]
pub struct LogConfig {
    /// Global log level (0-10)
    pub global_level: u8,

    /// Per-scope overrides
    pub scopes: HashMap<String, u8>,

    /// Whether to include timestamps
    pub timestamps: bool,

    /// Whether to include file:line
    pub locations: bool,

    /// Output format
    pub format: LogFormat,
}

#[derive(Debug, Clone)]
pub enum LogFormat {
    Text,      // Human readable
    Json,      // Machine parseable
    Compact,   // Minimal
}

impl LogConfig {
    /// Get effective level for scope
    pub fn level_for(&self, scope: &str) -> u8 {
        self.scopes.get(scope).copied().unwrap_or(self.global_level)
    }

    /// Check if should log at level for scope
    pub fn should_log(&self, level: u8, scope: &str) -> bool {
        level <= self.level_for(scope)
    }
}

/// Predefined configurations
impl LogConfig {
    pub fn production() -> Self {
        Self {
            global_level: 3, // Warn and above
            scopes: HashMap::new(),
            timestamps: true,
            locations: false,
            format: LogFormat::Json,
        }
    }

    pub fn development() -> Self {
        Self {
            global_level: 5, // Debug and above
            scopes: HashMap::new(),
            timestamps: true,
            locations: true,
            format: LogFormat::Text,
        }
    }

    pub fn testing() -> Self {
        Self {
            global_level: 6, // Trace and above
            scopes: HashMap::new(),
            timestamps: false,
            locations: true,
            format: LogFormat::Text,
        }
    }

    pub fn sdn() -> Self {
        Self {
            global_level: 2, // Error only
            scopes: HashMap::new(),
            timestamps: false,
            locations: false,
            format: LogFormat::Compact,
        }
    }
}
```

### Scope-based Filtering

```rust
// Example scope configuration
let mut config = LogConfig::development();
config.scopes.insert("parser".to_string(), 3);      // Parser at warn
config.scopes.insert("interpreter".to_string(), 6); // Interpreter at trace
config.scopes.insert("gc".to_string(), 4);          // GC at info
config.scopes.insert("codegen".to_string(), 5);     // Codegen at debug
```

### SDN Configuration File

```sdn
# config/log.sdn
log:
    global_level: 5
    timestamps: true
    locations: true
    format: "text"

    scopes |name, level|
        parser, 3
        interpreter, 6
        gc, 4
        codegen, 5
        sdn, 2
```

---

## Dependency Injection System

### Container Interface

```rust
// src/rust/hir-core/src/di.rs

use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::sync::Arc;

/// Service trait - all injectable services implement this
pub trait Service: Any + Send + Sync {
    fn as_any(&self) -> &dyn Any;
}

/// Factory function type
pub type Factory = Arc<dyn Fn(&Container) -> Arc<dyn Service> + Send + Sync>;

/// DI Container with profile support
#[derive(Clone)]
pub struct Container {
    /// Current profile
    profile: Profile,

    /// Service bindings
    bindings: HashMap<TypeId, Factory>,

    /// Singleton instances
    singletons: HashMap<TypeId, Arc<dyn Service>>,

    /// Parent container (for scoped resolution)
    parent: Option<Arc<Container>>,
}

/// Profile enum
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Profile {
    Test,       // Mock services, full logging
    Dev,        // Full services, debug logging
    Prod,       // Optimized services, warn logging
    Sdn,        // NoOp instructions, error logging only
}

impl Container {
    /// Create container with profile
    pub fn with_profile(profile: Profile) -> Self {
        let mut container = Self {
            profile,
            bindings: HashMap::new(),
            singletons: HashMap::new(),
            parent: None,
        };
        container.register_defaults();
        container
    }

    /// Register default bindings based on profile
    fn register_defaults(&mut self) {
        match self.profile {
            Profile::Test => {
                self.bind::<dyn InstructionModule>(|| Arc::new(MockInstructionModule));
                self.bind::<dyn LogConfig>(|| Arc::new(LogConfig::testing()));
            }
            Profile::Dev => {
                self.bind::<dyn InstructionModule>(|| Arc::new(FullInstructionModule));
                self.bind::<dyn LogConfig>(|| Arc::new(LogConfig::development()));
            }
            Profile::Prod => {
                self.bind::<dyn InstructionModule>(|| Arc::new(OptimizedInstructionModule));
                self.bind::<dyn LogConfig>(|| Arc::new(LogConfig::production()));
            }
            Profile::Sdn => {
                // SDN profile: NoOp instructions prevent code execution
                self.bind::<dyn InstructionModule>(|| Arc::new(NoOpInstructionModule));
                self.bind::<dyn LogConfig>(|| Arc::new(LogConfig::sdn()));
            }
        }
    }

    /// Bind a service factory
    pub fn bind<T: Service + ?Sized>(&mut self, factory: impl Fn() -> Arc<T> + Send + Sync + 'static) {
        let type_id = TypeId::of::<T>();
        self.bindings.insert(type_id, Arc::new(move |_| factory() as Arc<dyn Service>));
    }

    /// Resolve a service
    pub fn resolve<T: Service + ?Sized>(&self) -> Option<Arc<T>> {
        let type_id = TypeId::of::<T>();

        // Check singletons first
        if let Some(instance) = self.singletons.get(&type_id) {
            return Some(instance.clone().as_any().downcast_ref::<T>()?.clone());
        }

        // Check bindings
        if let Some(factory) = self.bindings.get(&type_id) {
            let instance = factory(self);
            return Some(instance.as_any().downcast_ref::<T>()?.clone());
        }

        // Check parent
        if let Some(parent) = &self.parent {
            return parent.resolve::<T>();
        }

        None
    }

    /// Create child scope
    pub fn scope(&self) -> Container {
        Container {
            profile: self.profile,
            bindings: HashMap::new(),
            singletons: HashMap::new(),
            parent: Some(Arc::new(self.clone())),
        }
    }
}
```

### Instruction Module Interface

```rust
// src/rust/hir-core/src/instruction.rs

/// Instruction module - injected into interpreter/compiler
pub trait InstructionModule: Service {
    /// Execute a high-level instruction
    fn execute(&self, inst: &HirInstruction, ctx: &mut ExecutionContext) -> Result<Value, Error>;

    /// Check if instruction is allowed
    fn is_allowed(&self, inst: &HirInstruction) -> bool;

    /// Get instruction cost (for optimization)
    fn cost(&self, inst: &HirInstruction) -> u32;
}

/// Full instruction module - executes everything
pub struct FullInstructionModule;

impl InstructionModule for FullInstructionModule {
    fn execute(&self, inst: &HirInstruction, ctx: &mut ExecutionContext) -> Result<Value, Error> {
        // Full implementation
        match inst {
            HirInstruction::LoadConst(val) => Ok(val.clone()),
            HirInstruction::Call { func, args } => self.execute_call(func, args, ctx),
            HirInstruction::FieldGet { obj, field } => self.execute_field_get(obj, field, ctx),
            // ... all instructions
        }
    }

    fn is_allowed(&self, _inst: &HirInstruction) -> bool {
        true // All allowed
    }

    fn cost(&self, inst: &HirInstruction) -> u32 {
        match inst {
            HirInstruction::LoadConst(_) => 1,
            HirInstruction::Call { .. } => 10,
            HirInstruction::FieldGet { .. } => 2,
            // ...
        }
    }
}

/// NoOp instruction module - blocks code execution (for SDN)
pub struct NoOpInstructionModule;

impl InstructionModule for NoOpInstructionModule {
    fn execute(&self, inst: &HirInstruction, _ctx: &mut ExecutionContext) -> Result<Value, Error> {
        match inst {
            // Only allow data literals
            HirInstruction::LoadConst(val) => Ok(val.clone()),
            HirInstruction::ArrayNew(elements) => {
                // Allow array literals
                Ok(Value::Array(elements.clone()))
            }
            HirInstruction::DictNew(pairs) => {
                // Allow dict literals
                Ok(Value::Dict(pairs.clone()))
            }
            // Block everything else
            _ => Err(Error::new("Code execution not allowed in SDN mode"))
        }
    }

    fn is_allowed(&self, inst: &HirInstruction) -> bool {
        matches!(inst,
            HirInstruction::LoadConst(_) |
            HirInstruction::ArrayNew(_) |
            HirInstruction::DictNew(_)
        )
    }

    fn cost(&self, _inst: &HirInstruction) -> u32 {
        0 // NoOp is free
    }
}

/// Mock instruction module - for testing
pub struct MockInstructionModule {
    /// Recorded instructions
    pub recorded: Vec<HirInstruction>,
}

impl InstructionModule for MockInstructionModule {
    fn execute(&self, inst: &HirInstruction, ctx: &mut ExecutionContext) -> Result<Value, Error> {
        self.recorded.push(inst.clone());
        // Return mock values
        Ok(Value::None)
    }

    fn is_allowed(&self, _inst: &HirInstruction) -> bool {
        true
    }

    fn cost(&self, _inst: &HirInstruction) -> u32 {
        1
    }
}
```

---

## AOP for Logging

### Pointcut Definitions

```rust
// src/rust/hir-core/src/aop.rs

/// Pointcut - defines where advice applies
#[derive(Debug, Clone)]
pub enum Pointcut {
    /// Match all instructions of a type
    Instruction(InstructionKind),

    /// Match all calls to a function
    Call { function: String },

    /// Match all field access
    FieldAccess { class: Option<String>, field: Option<String> },

    /// Match by scope
    Scope { scope: String },

    /// Match by log level
    LogLevel { min_level: u8 },

    /// Combine pointcuts
    And(Box<Pointcut>, Box<Pointcut>),
    Or(Box<Pointcut>, Box<Pointcut>),
    Not(Box<Pointcut>),
}

/// Advice - action to take at pointcut
#[derive(Debug, Clone)]
pub enum Advice {
    /// Log before execution
    LogBefore { level: u8, message: String },

    /// Log after execution
    LogAfter { level: u8, message: String },

    /// Log on error
    LogError { level: u8 },

    /// Time execution
    TimeExecution { scope: String },

    /// Custom advice
    Custom { handler: Arc<dyn AdviceHandler> },
}

/// Aspect - combines pointcut and advice
#[derive(Debug, Clone)]
pub struct Aspect {
    pub name: String,
    pub pointcut: Pointcut,
    pub advice: Vec<Advice>,
    pub enabled: bool,
}

/// AOP configuration
#[derive(Debug, Clone)]
pub struct AopConfig {
    pub aspects: Vec<Aspect>,
    pub enabled: bool,
}

impl AopConfig {
    /// Default logging aspects
    pub fn with_logging() -> Self {
        Self {
            aspects: vec![
                // Log all function calls at debug level
                Aspect {
                    name: "call_logging".to_string(),
                    pointcut: Pointcut::Instruction(InstructionKind::Call),
                    advice: vec![
                        Advice::LogBefore { level: 5, message: "Calling {function}".to_string() },
                        Advice::LogAfter { level: 5, message: "Returned from {function}".to_string() },
                    ],
                    enabled: true,
                },
                // Log errors
                Aspect {
                    name: "error_logging".to_string(),
                    pointcut: Pointcut::LogLevel { min_level: 2 },
                    advice: vec![
                        Advice::LogError { level: 2 },
                    ],
                    enabled: true,
                },
                // Time execution for performance
                Aspect {
                    name: "timing".to_string(),
                    pointcut: Pointcut::Scope { scope: "perf".to_string() },
                    advice: vec![
                        Advice::TimeExecution { scope: "perf".to_string() },
                    ],
                    enabled: false, // Disabled by default
                },
            ],
            enabled: true,
        }
    }
}
```

### AOP Weaver

```rust
// src/rust/hir-core/src/weaver.rs

/// Weaves aspects into instruction execution
pub struct Weaver {
    config: AopConfig,
    log_config: LogConfig,
}

impl Weaver {
    pub fn new(config: AopConfig, log_config: LogConfig) -> Self {
        Self { config, log_config }
    }

    /// Execute instruction with AOP
    pub fn execute_with_aspects(
        &self,
        inst: &HirInstruction,
        module: &dyn InstructionModule,
        ctx: &mut ExecutionContext,
    ) -> Result<Value, Error> {
        if !self.config.enabled {
            return module.execute(inst, ctx);
        }

        // Find matching aspects
        let aspects: Vec<_> = self.config.aspects.iter()
            .filter(|a| a.enabled && self.matches(&a.pointcut, inst))
            .collect();

        // Execute before advice
        for aspect in &aspects {
            for advice in &aspect.advice {
                self.execute_before(advice, inst, ctx);
            }
        }

        // Execute instruction
        let result = module.execute(inst, ctx);

        // Execute after advice
        for aspect in &aspects {
            for advice in &aspect.advice {
                self.execute_after(advice, inst, &result, ctx);
            }
        }

        result
    }

    fn matches(&self, pointcut: &Pointcut, inst: &HirInstruction) -> bool {
        match pointcut {
            Pointcut::Instruction(kind) => inst.kind() == *kind,
            Pointcut::Call { function } => {
                if let HirInstruction::Call { func, .. } = inst {
                    func == function || function == "*"
                } else {
                    false
                }
            }
            Pointcut::Scope { scope } => {
                self.log_config.should_log(5, scope) // Use debug level as threshold
            }
            Pointcut::And(a, b) => self.matches(a, inst) && self.matches(b, inst),
            Pointcut::Or(a, b) => self.matches(a, inst) || self.matches(b, inst),
            Pointcut::Not(p) => !self.matches(p, inst),
            _ => false,
        }
    }

    fn execute_before(&self, advice: &Advice, inst: &HirInstruction, ctx: &mut ExecutionContext) {
        match advice {
            Advice::LogBefore { level, message } => {
                if self.log_config.should_log(*level, "aop") {
                    let msg = self.format_message(message, inst, ctx);
                    log(*level, "aop", &msg);
                }
            }
            Advice::TimeExecution { scope } => {
                ctx.start_timer(scope);
            }
            _ => {}
        }
    }

    fn execute_after(&self, advice: &Advice, inst: &HirInstruction, result: &Result<Value, Error>, ctx: &mut ExecutionContext) {
        match advice {
            Advice::LogAfter { level, message } => {
                if self.log_config.should_log(*level, "aop") {
                    let msg = self.format_message(message, inst, ctx);
                    log(*level, "aop", &msg);
                }
            }
            Advice::LogError { level } => {
                if let Err(e) = result {
                    if self.log_config.should_log(*level, "aop") {
                        log(*level, "aop", &format!("Error: {}", e));
                    }
                }
            }
            Advice::TimeExecution { scope } => {
                if let Some(elapsed) = ctx.stop_timer(scope) {
                    log(6, "perf", &format!("{}: {:?}", scope, elapsed));
                }
            }
            _ => {}
        }
    }
}
```

---

## Parser Two-Layer Design

### Outline Parser (High-Level)

```rust
// src/rust/parser/src/outline.rs

/// Outline module - quick parse for tooling
#[derive(Debug, Clone)]
pub struct OutlineModule {
    /// Module path
    pub path: String,

    /// Imports
    pub imports: Vec<OutlineImport>,

    /// Type declarations (struct, class, enum)
    pub types: Vec<OutlineType>,

    /// Function signatures (no bodies)
    pub functions: Vec<OutlineFunction>,

    /// Trait declarations
    pub traits: Vec<OutlineTrait>,

    /// Exports
    pub exports: Vec<String>,

    /// Spans for syntax highlighting
    pub spans: Vec<(Span, TokenKind)>,
}

#[derive(Debug, Clone)]
pub struct OutlineFunction {
    pub name: String,
    pub params: Vec<(String, Option<String>)>, // (name, type)
    pub return_type: Option<String>,
    pub is_async: bool,
    pub is_pub: bool,
    pub span: Span,
    // No body - that's parsed in full mode
}

#[derive(Debug, Clone)]
pub struct OutlineType {
    pub kind: TypeKind, // Struct, Class, Enum
    pub name: String,
    pub generics: Vec<String>,
    pub fields: Vec<(String, String)>, // (name, type)
    pub is_pub: bool,
    pub span: Span,
}

/// Outline parser
pub struct OutlineParser {
    container: Container,
}

impl OutlineParser {
    pub fn new(container: Container) -> Self {
        Self { container }
    }

    /// Quick parse - declarations only
    pub fn parse_outline(&self, source: &str) -> Result<OutlineModule, ParseError> {
        let log = self.container.resolve::<LogConfig>().unwrap();

        if log.should_log(6, "parser") {
            log(6, "parser", "Starting outline parse");
        }

        let tokens = self.tokenize(source)?;
        let outline = self.parse_declarations(&tokens)?;

        if log.should_log(6, "parser") {
            log(6, "parser", &format!("Outline: {} types, {} functions",
                outline.types.len(), outline.functions.len()));
        }

        Ok(outline)
    }

    /// TreeSitter compatible output
    pub fn to_tree_sitter(&self, outline: &OutlineModule) -> TreeSitterTree {
        // Convert to TreeSitter tree structure
        // This allows IDE integration
        todo!()
    }
}
```

### Full Parser (Low-Level)

```rust
// src/rust/parser/src/full.rs

/// Full module - complete AST
pub struct FullModule {
    /// Outline information
    pub outline: OutlineModule,

    /// Complete function bodies
    pub functions: HashMap<String, FunctionDef>,

    /// Type information with resolved generics
    pub types: HashMap<String, TypeDef>,

    /// Effect annotations
    pub effects: HashMap<String, Effect>,

    /// Macro expansions
    pub macro_expansions: Vec<MacroExpansion>,
}

/// Full parser - complete parse with type resolution
pub struct FullParser {
    container: Container,
    outline_parser: OutlineParser,
}

impl FullParser {
    pub fn new(container: Container) -> Self {
        Self {
            outline_parser: OutlineParser::new(container.clone()),
            container,
        }
    }

    /// Full parse - complete AST with types and effects
    pub fn parse_full(&self, source: &str) -> Result<FullModule, ParseError> {
        let log = self.container.resolve::<LogConfig>().unwrap();

        // First do outline parse
        let outline = self.outline_parser.parse_outline(source)?;

        if log.should_log(5, "parser") {
            log(5, "parser", "Starting full parse");
        }

        // Parse function bodies
        let functions = self.parse_function_bodies(source, &outline)?;

        // Resolve types
        let types = self.resolve_types(&outline, &functions)?;

        // Infer effects
        let effects = self.infer_effects(&functions)?;

        if log.should_log(5, "parser") {
            log(5, "parser", "Full parse complete");
        }

        Ok(FullModule {
            outline,
            functions,
            types,
            effects,
            macro_expansions: vec![],
        })
    }
}
```

---

## Shared HIR Instructions

### Instruction Enum

```rust
// src/rust/hir-core/src/instruction.rs

/// High-level IR instruction - shared by interpreter and compiler
#[derive(Debug, Clone, PartialEq)]
pub enum HirInstruction {
    // === Data Operations ===
    /// Load constant value
    LoadConst(Value),
    /// Load local variable
    LoadLocal { slot: u32 },
    /// Store to local variable
    StoreLocal { slot: u32 },
    /// Binary operation
    BinOp { op: BinOpKind, left: Box<HirInstruction>, right: Box<HirInstruction> },
    /// Unary operation
    UnaryOp { op: UnaryOpKind, operand: Box<HirInstruction> },

    // === Control Flow ===
    /// Conditional branch
    Branch { condition: Box<HirInstruction>, then_block: Vec<HirInstruction>, else_block: Vec<HirInstruction> },
    /// Unconditional jump
    Jump { target: Label },
    /// Function call
    Call { func: String, args: Vec<HirInstruction> },
    /// Method call
    MethodCall { receiver: Box<HirInstruction>, method: String, args: Vec<HirInstruction> },
    /// Return from function
    Return { value: Option<Box<HirInstruction>> },
    /// Pattern match
    Match { scrutinee: Box<HirInstruction>, arms: Vec<MatchArm> },

    // === Object Operations ===
    /// Get field value
    FieldGet { object: Box<HirInstruction>, field: String },
    /// Set field value
    FieldSet { object: Box<HirInstruction>, field: String, value: Box<HirInstruction> },
    /// Construct object
    Construct { class: String, fields: Vec<(String, HirInstruction)> },
    /// Array literal
    ArrayNew(Vec<HirInstruction>),
    /// Dict literal
    DictNew(Vec<(HirInstruction, HirInstruction)>),

    // === Constraint Operations ===
    /// Runtime type assertion
    TypeAssert { value: Box<HirInstruction>, expected: String },
    /// Capability check (mut, iso, etc.)
    CapabilityCheck { value: Box<HirInstruction>, capability: Capability },
    /// Contract precondition
    Precondition { condition: Box<HirInstruction>, message: String },
    /// Contract postcondition
    Postcondition { condition: Box<HirInstruction>, message: String },
    /// Class invariant
    Invariant { condition: Box<HirInstruction>, message: String },

    // === Effect Operations ===
    /// Effect boundary marker
    EffectBoundary { effect: Effect },
    /// Suspend execution (for async/generator)
    Suspend { value: Option<Box<HirInstruction>> },
    /// Resume execution
    Resume { value: Option<Box<HirInstruction>> },

    // === Memory Operations ===
    /// Allocate memory
    Alloc { layout: StructLayout },
    /// Deallocate memory
    Dealloc { ptr: Box<HirInstruction> },
    /// Reference count increment
    RefInc { ptr: Box<HirInstruction> },
    /// Reference count decrement
    RefDec { ptr: Box<HirInstruction> },
    /// GC safepoint
    GcSafepoint,
}

/// Get instruction kind for AOP matching
impl HirInstruction {
    pub fn kind(&self) -> InstructionKind {
        match self {
            HirInstruction::LoadConst(_) => InstructionKind::LoadConst,
            HirInstruction::LoadLocal { .. } => InstructionKind::LoadLocal,
            HirInstruction::StoreLocal { .. } => InstructionKind::StoreLocal,
            HirInstruction::BinOp { .. } => InstructionKind::BinOp,
            HirInstruction::Call { .. } => InstructionKind::Call,
            HirInstruction::MethodCall { .. } => InstructionKind::MethodCall,
            HirInstruction::FieldGet { .. } => InstructionKind::FieldGet,
            HirInstruction::FieldSet { .. } => InstructionKind::FieldSet,
            // ...
            _ => InstructionKind::Other,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstructionKind {
    LoadConst,
    LoadLocal,
    StoreLocal,
    BinOp,
    UnaryOp,
    Branch,
    Jump,
    Call,
    MethodCall,
    Return,
    Match,
    FieldGet,
    FieldSet,
    Construct,
    ArrayNew,
    DictNew,
    TypeAssert,
    CapabilityCheck,
    Precondition,
    Postcondition,
    Invariant,
    EffectBoundary,
    Suspend,
    Resume,
    Alloc,
    Dealloc,
    RefInc,
    RefDec,
    GcSafepoint,
    Other,
}
```

---

## Initialization with DI

### Application Bootstrap

```rust
// src/rust/driver/src/init.rs

/// Initialize application with DI
pub fn init(profile: Profile) -> Result<Application, Error> {
    // Create container with profile
    let container = Container::with_profile(profile);

    // Register additional services
    let mut container = container;
    container.bind::<dyn Parser>(|| {
        let inner = container.clone();
        Arc::new(FullParser::new(inner))
    });
    container.bind::<dyn Executor>(|| {
        let inner = container.clone();
        Arc::new(create_executor(inner))
    });

    // Create AOP config
    let aop_config = match profile {
        Profile::Test => AopConfig::with_logging(),
        Profile::Dev => AopConfig::with_logging(),
        Profile::Prod => AopConfig { aspects: vec![], enabled: false },
        Profile::Sdn => AopConfig { aspects: vec![], enabled: false },
    };

    // Create weaver
    let log_config = container.resolve::<LogConfig>().unwrap();
    let weaver = Weaver::new(aop_config, (*log_config).clone());

    Ok(Application {
        container,
        weaver,
    })
}

/// Create executor based on container
fn create_executor(container: Container) -> Box<dyn Executor> {
    let inst_module = container.resolve::<dyn InstructionModule>().unwrap();
    let log_config = container.resolve::<LogConfig>().unwrap();

    match container.profile {
        Profile::Sdn => {
            // SDN: Interpreter with NoOp instructions
            Box::new(InterpreterExecutor::new(inst_module, log_config))
        }
        Profile::Test | Profile::Dev => {
            // Dev/Test: Interpreter with full instructions
            Box::new(InterpreterExecutor::new(inst_module, log_config))
        }
        Profile::Prod => {
            // Prod: JIT compiler
            Box::new(JitExecutor::new(inst_module, log_config))
        }
    }
}
```

### SDN Safe Initialization

```rust
// src/rust/sdn/src/lib.rs

/// Parse SDN with safety guarantees
pub fn parse_document_safe(source: &str) -> Result<SdnDocument, SdnError> {
    // Use SDN profile - NoOp instructions
    let container = Container::with_profile(Profile::Sdn);

    // Get NoOp instruction module
    let inst_module = container.resolve::<dyn InstructionModule>().unwrap();

    // Verify it's actually NoOp
    assert!(!inst_module.is_allowed(&HirInstruction::Call {
        func: "dangerous".to_string(),
        args: vec![]
    }));

    // Parse with safety
    let parser = SdnParser::new(container);
    parser.parse(source)
}
```

---

## Configuration File Format

### Main Configuration (config.sdn)

```sdn
# Application configuration

profile: "dev"  # test | dev | prod | sdn

log:
    global_level: 5
    timestamps: true
    locations: true
    format: "text"

    scopes |name, level|
        parser, 3
        interpreter, 6
        gc, 4
        codegen, 5
        aop, 5

di:
    # Override default bindings
    bindings |interface, implementation|
        InstructionModule, "FullInstructionModule"
        Executor, "InterpreterExecutor"

aop:
    enabled: true

    aspects |name, pointcut, advice, enabled|
        call_logging, "call:*", "log_before:5,log_after:5", true
        error_logging, "level:2", "log_error:2", true
        timing, "scope:perf", "time_execution", false

mode:
    execution: "interpret"  # interpret | jit | aot
    debug: true
    optimize: false
```

---

## Summary

| Component | Purpose | Key Types |
|-----------|---------|-----------|
| **LogConfig** | 10-level logging | `LogLevel`, `LogConfig`, scope filtering |
| **DiConfig** | Dependency injection | `Container`, `Profile`, `Service` |
| **AopConfig** | Aspect-oriented programming | `Aspect`, `Pointcut`, `Advice`, `Weaver` |
| **HirInstruction** | Shared instruction model | 30+ instruction types |
| **OutlineParser** | Quick parse for tooling | `OutlineModule`, TreeSitter compat |
| **FullParser** | Complete parse | `FullModule`, type resolution |
| **InstructionModule** | Inject instruction behavior | `FullInstructionModule`, `NoOpInstructionModule` |

### Key Benefits

1. **SDN Safety**: NoOp instructions prevent code execution in data files
2. **Unified Logging**: 10 levels with scope filtering
3. **Testability**: Mock instruction modules for testing
4. **Tooling Support**: Outline parser for IDE integration
5. **Shared Logic**: HIR instructions used by both interpreter and compiler
6. **Configurability**: All behavior controllable via config files
