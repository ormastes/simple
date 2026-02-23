# DI & Composition Root Design: Seeing All Connections in One Place

> How should Simple wire application dependencies so the full connection map
> is visible from a single file?
>
> Analyzes current state, identifies gaps, proposes design options.

**Date:** 2026-02-17
**Status:** Research / Design Proposal
**Related:** `compiler_mdsoc_design.md`, `standard_architecture.md`, `compiler_mdsoc_impl_plan.md`

---

## 1. Problem Statement

**Goal:** Open ONE file and see every service the application needs, what interface
each service must satisfy, and which concrete implementation is wired.

**Current state fails this goal.** The compiler's composition root (`CompileContext`)
uses two incompatible patterns:

```
CompileContext (driver_types.spl:264-332)
├── options: CompileOptions          ← TYPED (visible contract)
├── config: Dict<text, text>         ← TYPED (visible)
├── logger: Logger                   ← TYPED (visible)
├── aop: AopWeaver                   ← TYPED (visible)
├── di: DiContainer                  ← BLACK BOX
│   └── "Backend" → Any             ← hidden type, hidden interface
├── sources: [SourceFile]            ← TYPED (visible)
├── modules: Dict<text, Module>      ← TYPED (visible)
├── hir_modules: Dict<text, HirModule>  ← TYPED (visible)
└── mir_modules: Dict<text, MirModule>  ← TYPED (visible)
```

**Three problems with `di: DiContainer`:**

1. **Hidden contract:** `di.resolve("Backend")` returns `Any`. You can't see
   what methods/fields the backend must have without reading every call site.

2. **String-keyed:** Typo in `"Backend"` → runtime panic, not compile error.
   No autocomplete, no refactoring support.

3. **Scattered resolution:** `di.resolve("Backend")` is called in `driver.spl`
   at multiple points. The binding (`bind_instance`) is in `driver_types.spl`.
   You must read BOTH files to see the connection.

**Contrast with typed fields:** `logger: Logger` on `CompileContext` tells you:
- The compiler needs a logger
- It must be of type `Logger`
- It's set in `CompileContext.create()`
- It's used via `self.logger`

All visible from one struct definition.

---

## 2. Current DI Infrastructure Inventory

### 2.1 `src/compiler/di.spl` (147 lines)

```simple
class DiContainer:
    bindings: Dict<text, fn() -> Any>    # lazy factories
    singletons: Dict<text, Any>          # eager instances
    profile: text                         # dev/test/prod/sdn

    me bind(name, factory)               # register lazy factory
    me bind_instance(name, instance)     # register eager singleton
    fn resolve(name) -> Any              # lookup (singletons first)
    fn resolve_or(name, default) -> Any  # safe lookup with fallback
    fn has(name) -> bool                 # existence check
    me resolve_singleton(name) -> Any    # resolve + cache
```

**Capabilities:**
- Profile-based binding (`bind_for_profile`)
- Tagged binding (`bind_tagged`)
- Singleton caching (`resolve_singleton`)
- Global container (`set_container`, `get_container`)

**Limitations:**
- Returns `Any` (no type safety)
- String keys (no compile-time validation)
- No required-bindings manifest
- No lifecycle management (scoped, lazy)
- No circular dependency detection
- No auto-wiring

### 2.2 `src/lib/src/di.spl` (~200 lines)

Separate stdlib DI with profile factories (`for_test()`, `for_dev()`, etc.).
Similar pattern to compiler DI, different implementation.

### 2.3 Usage: Only 1 Service in DI

In practice, **only "Backend"** goes through `DiContainer`:

```simple
# Binding (driver_types.spl:286-306)
di.bind_instance("Backend", InterpreterBackendImpl.with_config(...))
di.bind_instance("Backend", CompilerBackendImpl.jit())
# etc.

# Resolution (driver.spl, scattered)
val backend = self.ctx.di.resolve("Backend")
```

Everything else (`logger`, `aop`, `config`, `modules`) is a typed field.
The DI container holds exactly ONE service.

### 2.4 Backend Factory (backend_factory.spl, ~200 lines)

Separate from DI. Used for AOT compilation backend selection:

```simple
BackendFactory.create(target, options) → Backend
BackendFactory.auto_select(target, mode) → BackendKind
```

Not connected to `DiContainer` — parallel wiring path.

---

## 3. What "All Connections in One Place" Means

### 3.1 The Composition Root Pattern

A **composition root** is the single location where:

1. All service **contracts** (ports/interfaces) are defined or referenced
2. All **concrete implementations** are selected and wired
3. The **dependency graph** is fully visible

**In Spring (Java):** `@Configuration` class with `@Bean` methods.
**In .NET:** `Startup.ConfigureServices()` with `services.AddX()`.
**In Go:** `func main()` with manual construction.
**In Rust:** `fn main()` building structs with trait object fields.

### 3.2 What Simple Needs

Opening ONE struct definition should answer:

| Question | Answer should be visible |
|----------|-------------------------|
| What services exist? | Struct fields list them all |
| What interface each needs? | Field type is the port struct |
| Which impl is wired? | Factory function in `create()` |
| Can I swap for testing? | Pass different factory |
| What's missing? | Compiler error: field not set |

---

## 4. Design Options

### Option A: Pure Typed Container (No DI Framework)

**Eliminate `DiContainer` entirely.** Move Backend to a typed field.

```simple
struct CompileContext:
    options: CompileOptions
    backend: BackendPort          # ← was di.resolve("Backend")
    logger: Logger
    aop: AopWeaver
    config: Dict<text, text>
    sources: [SourceFile]
    modules: Dict<text, Module>
    hir_modules: Dict<text, HirModule>
    mir_modules: Dict<text, MirModule>
    errors: [text]
    warnings: [text]

struct BackendPort:
    """Contract: what the compiler needs from a backend."""
    name: text
    run_fn: fn(Module) -> CompileResult
    supports_jit_fn: fn() -> bool
    target_triple: text
```

**Factory per mode:**

```simple
fn create_context(options: CompileOptions) -> CompileContext:
    val backend = match options.mode:
        case CompileMode.Interpret:
            make_interpreter_backend(options)
        case CompileMode.Jit:
            make_jit_backend(options)
        case CompileMode.Aot:
            make_aot_backend(options)
        case CompileMode.Sdn:
            make_sdn_backend()
        case CompileMode.Check:
            make_check_backend()

    CompileContext(
        options: options,
        backend: backend,        # ← visible, typed
        logger: make_logger(options),
        aop: make_aop(options),
        config: {},
        sources: [],
        modules: {},
        hir_modules: {},
        mir_modules: {},
        errors: [],
        warnings: []
    )
```

**Evaluation:**

| Criterion | Score | Notes |
|-----------|-------|-------|
| All connections visible | +++   | Every service is a typed field |
| Compile-time safety     | +++   | Missing field = compile error |
| Dynamic registration    | ---   | Can't add services at runtime |
| Plugin support          | ---   | No open registry |
| Complexity              | +++   | Simplest option, no framework |
| Testing                 | ++    | Pass different factory function |
| Current language support| +++   | Works today, no new features |

**Verdict:** Best for seeing all connections. Loses dynamic capability.

---

### Option B: Typed Container + DI Overlay

**Keep typed fields for core services. Keep DI for optional/plugin services.**

```simple
struct CompileContext:
    # === CORE SERVICES (typed, always present) ===
    backend: BackendPort
    logger: Logger
    aop: AopWeaver
    module_loader: ModuleLoaderPort

    # === OPTIONAL SERVICES (DI, for plugins/extensions) ===
    extensions: DiContainer

    # === STATE (not services) ===
    options: CompileOptions
    sources: [SourceFile]
    modules: Dict<text, Module>
    # ...
```

**Usage:**

```simple
# Core services: direct field access (fast, type-safe)
self.backend.run_fn(module)
self.logger.log("compiling...")

# Extensions: DI lookup (dynamic, for plugins)
val profiler = self.extensions.resolve_or("Profiler", nil)
if profiler != nil:
    profiler.start_phase("parsing")
```

**Evaluation:**

| Criterion | Score | Notes |
|-----------|-------|-------|
| All connections visible | ++    | Core visible, extensions dynamic |
| Compile-time safety     | ++    | Core typed, extensions Any |
| Dynamic registration    | ++    | Via extensions container |
| Plugin support          | ++    | Plugins register in extensions |
| Complexity              | +     | Two systems to understand |
| Testing                 | ++    | Swap core factories + mock extensions |
| Current language support| +++   | Works today |

**Verdict:** Pragmatic middle ground. Core visible, plugins dynamic.

---

### Option C: DI Container with Typed Manifest

**Keep `DiContainer` but add a manifest struct declaring required bindings.**

```simple
struct CompilerManifest:
    """Declares ALL services the compiler needs.
    Open this struct to see every dependency."""
    backend: text = "Backend"
    logger: text = "Logger"
    aop: text = "AopWeaver"
    module_loader: text = "ModuleLoader"

fn validate_container(di: DiContainer, manifest: CompilerManifest) -> [text]:
    """Check that all required bindings exist."""
    var missing = []
    if not di.has(manifest.backend):
        missing.append("Missing required binding: {manifest.backend}")
    if not di.has(manifest.logger):
        missing.append("Missing required binding: {manifest.logger}")
    # ...
    missing
```

**Evaluation:**

| Criterion | Score | Notes |
|-----------|-------|-------|
| All connections visible | +     | Manifest lists names, not types |
| Compile-time safety     | -     | Validation at runtime only |
| Dynamic registration    | +++   | Full DI flexibility |
| Plugin support          | +++   | Open registry |
| Complexity              | +     | Manifest + container + validation |
| Testing                 | +     | Must validate before use |
| Current language support| +++   | Works today |

**Verdict:** Partial visibility. Names visible, types hidden.

---

### Option D: `service` Keyword (New Language Feature)

**Compiler-level service declaration with compile-time validation.**

```simple
# Define service contract (like trait but for DI)
service BackendService:
    """Compiler backend contract."""
    fn run(module: Module) -> CompileResult
    fn supports_jit() -> bool
    fn target_triple() -> text

# Implement service
provide BackendService as InterpreterBackend:
    fn run(module: Module) -> CompileResult:
        interpret(module)
    fn supports_jit() -> bool:
        false
    fn target_triple() -> text:
        "interpreter"

# Composition root
compose CompilerApp:
    require BackendService        # must be bound
    require LoggerService         # must be bound
    optional ProfilerService      # may be nil

    when mode == "test":
        bind BackendService to MockBackend
        bind LoggerService to NullLogger
    when mode == "prod":
        bind BackendService to LlvmBackend
        bind LoggerService to FileLogger

# Usage (services resolved from composition context)
fn compile(ctx: CompilerApp, source: text) -> CompileResult:
    ctx.BackendService.run(parse(source))
```

**Compiler validates:**
- All `require` services are bound in every `when` branch
- `provide` implementations match `service` signatures
- No circular dependencies between services

**Evaluation:**

| Criterion | Score | Notes |
|-----------|-------|-------|
| All connections visible | +++   | `compose` block shows everything |
| Compile-time safety     | +++   | Compiler validates completeness |
| Dynamic registration    | +     | `when` branches, not runtime |
| Plugin support          | +     | Would need `provide` in plugin modules |
| Complexity              | ++    | New syntax to learn |
| Testing                 | +++   | `when mode == "test"` built-in |
| Current language support| ---   | Requires parser + runtime changes |

**Verdict:** Best visibility + safety, but requires language changes.

---

### Option E: `trait` + Typed Container (Moderate Language Feature)

**Add `trait` keyword that desugars to struct-with-fn-fields.
Use typed container (Option A) with trait-based ports.**

```simple
# trait desugars to struct-with-fn-fields
trait BackendPort:
    fn run(module: Module) -> CompileResult
    fn supports_jit() -> bool
    fn target_triple() -> text

# Desugared by compiler to:
# struct BackendPort:
#     run_fn: fn(Module) -> CompileResult
#     supports_jit_fn: fn() -> bool
#     target_triple_fn: fn() -> text

# impl generates factory function
impl BackendPort for interpreter:
    fn run(module: Module) -> CompileResult:
        interpret(module)
    fn supports_jit() -> bool:
        false
    fn target_triple() -> text:
        "interpreter"

# Desugared to:
# fn interpreter_as_BackendPort() -> BackendPort:
#     BackendPort(
#         run_fn: interpreter_run,
#         supports_jit_fn: interpreter_supports_jit,
#         target_triple_fn: interpreter_target_triple
#     )

# Typed container (same as Option A)
struct CompileServices:
    backend: BackendPort
    logger: LoggerPort
    module_loader: ModuleLoaderPort
```

**Evaluation:**

| Criterion | Score | Notes |
|-----------|-------|-------|
| All connections visible | +++   | Typed container |
| Compile-time safety     | +++   | Struct field checks |
| Dynamic registration    | +     | Not built-in, but factory fns work |
| Plugin support          | +     | Plugins provide `impl` blocks |
| Complexity              | ++    | Familiar trait pattern |
| Testing                 | +++   | `impl BackendPort for mock: ...` |
| Current language support| --    | Needs parser + desugar pass |

**Verdict:** Clean, familiar, moderate effort. Solves "see all connections" fully.

---

## 5. Comparison Matrix

| Criterion | A: Typed | B: Typed+DI | C: Manifest | D: service | E: trait |
|-----------|----------|-------------|-------------|------------|---------|
| See all connections     | +++  | ++  | +   | +++ | +++ |
| Compile-time safety     | +++  | ++  | -   | +++ | +++ |
| Dynamic / plugins       | ---  | ++  | +++ | +   | +   |
| Works today (no changes)| YES  | YES | YES | NO  | NO  |
| Testing ergonomics      | ++   | ++  | +   | +++ | +++ |
| Complexity to implement | 0    | 0   | 0   | HIGH| MED |
| Migration effort        | LOW  | LOW | LOW | HIGH| MED |

---

## 6. Recommendation: Phased Approach

### Phase 1 (Now): Option A — Typed Container

**Zero language changes. Maximum visibility. Immediate benefit.**

Move `Backend` from DI to typed field on `CompileContext`:

```simple
struct CompileContext:
    backend: BackendPort    # ← replace di.resolve("Backend")
    logger: Logger
    aop: AopWeaver
    # ... rest unchanged
```

Define `BackendPort` as struct-with-fn-fields:

```simple
struct BackendPort:
    name: text
    run_fn: fn(Module) -> CompileResult
    supports_jit_fn: fn() -> bool
    target_triple_fn: fn() -> text
```

**Effort:** ~50 lines changed. Replace `di.resolve("Backend")` with `self.backend`.

**What this gives:**
- Open `CompileContext` struct → see ALL services
- Each service has a typed port → see contract
- Factory in `create()` → see wiring

### Phase 2 (Short-term): Option B overlay for plugins

Keep typed core. Add `extensions: DiContainer` for optional/plugin services
(profiler, doc-coverage hooks, IDE integration).

### Phase 3 (Mid-term): Option E — `trait` keyword

Add `trait` as syntactic sugar for struct-with-fn-fields:
- Reduces boilerplate for port definitions
- `impl` blocks auto-generate factory functions
- Familiar pattern from Rust/Go/Swift

### Phase 4 (Long-term): Consider Option D features

Selective additions from `service`/`compose` pattern:
- Required binding validation in `__init__.spl` arch blocks
- Conditional binding (`when mode ==`)
- Compile-time completeness checking

---

## 7. Applying to Standard Architecture

### 7.1 Current Compiler Pipeline

From `compiler_mdsoc_impl_plan.md`, each pipeline stage gets ports:

```simple
# ALL compiler services visible in one struct
struct CompilerServices:
    # Pipeline stages
    lexer: LexerPort
    parser: ParserPort
    desugarer: DesugarPort
    type_checker: TypeCheckPort
    hir_lowerer: HirLowerPort
    mir_lowerer: MirLowerPort
    optimizer: OptimizerPort
    backend: BackendPort

    # Cross-cutting
    logger: LoggerPort
    module_loader: ModuleLoaderPort
    diagnostics: DiagnosticsPort

    # Optional (nil = not configured)
    profiler: ProfilerPort?
    doc_coverage: DocCoveragePort?
```

**Open this ONE struct → see everything the compiler needs.**

### 7.2 Standard App Architecture

From `standard_architecture.md`:

```simple
struct AppServices:
    # Domain ports
    order_repo: OrderRepositoryPort
    payment: PaymentGatewayPort
    inventory: InventoryPort

    # Infrastructure ports
    clock: ClockPort
    mailer: MailerPort
    file_storage: FileStoragePort

    # Optional
    cache: CachePort?
    metrics: MetricsPort?
```

### 7.3 How DI Container Fits

The `DiContainer` remains useful for:

1. **Extension registration:** Plugins register services dynamically
2. **Profile switching:** `bind_for_profile("prod", ...)` for env-specific overrides
3. **Singleton management:** `resolve_singleton()` for expensive resources

But it should NOT hold **core services** that every caller needs.

**Rule:** If a service is used in >2 places → typed field.
If a service is optional/plugin → DI container.

---

## 8. Impact on Current Codebase

### 8.1 Files to Change (Phase 1)

| File | Change |
|------|--------|
| `src/compiler/driver_types.spl` | Add `backend: BackendPort` field, remove DI for Backend |
| `src/compiler/driver.spl` | Replace `di.resolve("Backend")` with `self.ctx.backend` |
| New: `src/compiler/backend_port.spl` | Define `BackendPort` struct |
| `src/compiler/di.spl` | Keep for extensions (unchanged) |

### 8.2 Files Unchanged

- `src/compiler/backend/*.spl` — backends unchanged, just wrapped in port
- `src/app/cli/main.spl` — CLI unchanged
- All test files — unchanged
- `src/compiler/mdsoc/` — unchanged (orthogonal to DI)

### 8.3 Backward Compatibility

- `DiContainer` stays available for stdlib users
- `CompileContext` gains a typed field, no fields removed
- `di` field can remain for backward compat (deprecated)

---

## 9. Feature Dependencies

### What works today (no language changes needed)

- Typed container struct (Option A)
- Factory functions returning port structs
- DI overlay for extensions (Option B)
- Manifest validation (Option C)

### What needs language features

| Feature | Dependency | Effort |
|---------|-----------|--------|
| `trait` keyword | Parser + desugar pass | Medium |
| `impl` blocks | Parser + desugar pass | Medium (same as trait) |
| `service`/`compose` | Parser + validator + runtime | High |
| Default field values | Parser + struct construction | Low-Medium |
| Structural subtyping | Type checker | Medium-High |
| Implicit context params | Parser + desugar + calling convention | High |
| Conditional compilation | Parser + compiler flags | Medium |

---

## 10. Comparison with Other Languages

### How Languages Solve "See All Connections"

| Language | Pattern | Visibility |
|----------|---------|------------|
| **Spring (Java)** | `@Configuration` class with `@Bean` methods | All beans in one config class |
| **.NET Core** | `Startup.ConfigureServices()` | All registrations in one method |
| **Angular** | `@NgModule({ providers: [...] })` | All providers in module decorator |
| **Go** | `func main()` manual wiring | All construction in main |
| **Rust** | `fn main()` building structs | All fields visible in struct def |
| **Dagger (Kotlin)** | `@Component` interface + `@Module` classes | Component interface lists all provisions |
| **Simple (current)** | `CompileContext.create()` + `di.resolve()` | **Split**: some visible, some hidden |
| **Simple (proposed)** | Typed container struct | All services as typed fields |

### Key Insight from Go and Rust

Go and Rust have NO DI framework in their standard ecosystems. They use:

1. **Interfaces/traits** define contracts
2. **Constructor functions** build implementations
3. **`main()` / composition root** wires everything manually
4. **Visibility is total** — every dependency is a function parameter or struct field

This works well because:
- Refactoring is safe (rename a type → compiler finds all uses)
- Missing dependency = compile error
- No magic, no reflection, no string keys
- Testing = pass mock implementation

Simple is closer to Go/Rust than to Spring/Angular.
The struct-with-fn-fields pattern IS Go's implicit interfaces.
The recommendation is to lean into this strength.

---

## References

- `doc/guide/standard_architecture.md` — Standard Simple architecture
- `doc/research/compiler_mdsoc_design.md` — Compiler pipeline MDSoC
- `doc/report/compiler_mdsoc_impl_plan.md` — Implementation plan
- `doc/research/mdsoc_design.md` — MDSoC dimension system
- `src/compiler/di.spl` — Current DI container
- `src/compiler/driver_types.spl` — Current composition root
