# Application Architecture Guide

Covers the two-layer language architecture and the standard application architecture (Clean / Hexagonal) for Simple programs.

---

## Two-Layer Language Architecture

Simple uses a two-layer design separating runtime execution from language implementation:

```
Layer 2: Simple Compiler & Tools (100% Simple)
  - Compiler (src/compiler/)
  - Standard Library (src/lib/)
  - Build System, MCP/LSP/DAP Servers, All Tools

Layer 1: Bootstrap Runtime (Pre-Compiled Binary)
  - LLVM/Cranelift Code Generation
  - Garbage Collector, FFI Bridge
  - Async I/O Runtime, Bytecode Executor
```

**Layer 1** provides the low-level execution environment (code generation, memory management, system calls). It ships as a pre-compiled binary (~10 MB).

**Layer 2** contains all user-visible functionality in 100% Simple source code (450,000+ lines). Users can read, modify, and extend the compiler without needing Rust.

### Distribution

| Included | Not Included |
|----------|-------------|
| Pre-compiled runtime binary | Rust source code |
| Complete compiler source | Build artifacts |
| Standard library source | Test files |
| All tools source | |

### Self-Hosting Bootstrap

```
Stage 1: Previous release compiles current compiler
Stage 2: New compiler recompiles itself
Stage 3: Verify identical output (checksums match)
```

```bash
simple build bootstrap
```

---

## Standard Application Architecture

Based on Clean Architecture / Hexagonal (Ports & Adapters), extended with MDSoC.

### Core Principle: Dependencies Point Inward

```
UI / Controllers          (volatile -- changes often)
    |
    v
Application / Use Cases   (orchestration)
    |
    v
Domain / Entities          (stable -- core logic)
```

Inner layers NEVER import outer layers. Outer layers import inner interfaces (ports).

### The Eight Principles

1. **Policy is stable, mechanisms are volatile** -- Domain + use-cases = policy; UI + DB = mechanisms
2. **Dependency Inversion at every IO boundary** -- Core defines ports, edge implements adapters
3. **One-direction dependency graph** -- No circular dependencies
4. **Explicit boundaries, explicit mapping** -- Map DTOs at layer boundaries
5. **Keep IO at the edges** -- Core has no network/filesystem/DB calls
6. **Thin adapters** -- Adapters translate and delegate only
7. **Composition root is the only global knowledge** -- Only wiring layer imports both core and adapters
8. **Test strategy aligns with boundaries** -- Unit-test core, integration-test adapters

### Three Layers

**Domain Layer** (`src/entity/`):

```simple
struct Order:
    id: text
    lines: [OrderLine]
    status: OrderStatus
    total: f64

    fn add_line(line: OrderLine):
        # Pure business logic, no framework dependencies
```

**Application Layer** (`src/feature/`):

```simple
struct CreateOrderUseCase:
    order_repo: OrderRepository     # Port (interface)
    payment: PaymentGateway         # Port (interface)

    fn execute(input: CreateOrderInput) -> Result<Order, text>:
        val order = Order.new(input.customer_id)
        # Orchestrate domain operations via ports
```

**Adapters** (`src/adapter/`):

```simple
# Inbound adapter (HTTP controller)
class OrderController:
    use_case: CreateOrderUseCase
    fn create(req) -> Response:
        val input = parse_request(req)
        val order = use_case.execute(input)?
        json(order)

# Outbound adapter (database)
class SqlOrderRepository impl OrderRepository:
    fn save(order: Order) -> Result<(), text>:
        db.execute("INSERT INTO orders ...", order.to_params())
```

### Directory Structure

```
src/
  entity/           # Domain layer (pure logic, no dependencies)
    Order/
    Product/
  feature/          # Application layer (use cases, ports)
    CreateOrder/
    ProcessPayment/
  adapter/          # Adapters (in: controllers, out: repos)
    http/
    persistence/
  composition/      # Wiring (dependency injection)
    app.spl
```

### Ports and Adapters

**Ports** are interfaces defined by the application layer:

```simple
trait OrderRepository:
    fn find_by_id(id: text) -> Option<Order>
    fn save(order: Order) -> Result<(), text>
```

**Adapters** implement ports for specific infrastructure:

```simple
class PostgresOrderRepository impl OrderRepository:
    fn find_by_id(id: text) -> Option<Order>:
        # PostgreSQL-specific implementation
```

### Multi-Dimensional Separation (MDSoC)

Simple extends Clean Architecture with dimensions:

- **Feature dimension:** Vertical slices (UI + app logic per feature)
- **Entity dimension:** Horizontal slices (domain entities by taxonomy)
- **Transform dimension:** Bridges between features and entities

### Testing Strategy

| Layer | Test Type | Dependencies |
|-------|-----------|-------------|
| Domain | Unit tests | None (pure logic) |
| Application | Unit tests | Mock ports |
| Adapters | Integration tests | Real infrastructure |
| End-to-end | System tests | Full stack |

### Common Anti-Patterns

- Putting business rules in controllers or adapters
- Domain entities importing framework/database types
- Sharing models across layers instead of mapping at boundaries
- Circular dependencies between modules

---

## Performance Characteristics

### Compilation Speed

~11ms per 1000 lines (debug mode), including lexing, parsing, type inference, MIR generation, and codegen.

### Runtime Performance

| Feature | Overhead vs Native |
|---------|-------------------|
| Function calls | 0% (inlined by LLVM) |
| Method dispatch | 0-5% (inline caching) |
| Generics | 0% (monomorphization) |
| GC allocation | 5-10% (generational GC) |

---

## Platform Support

| Tier | Platforms |
|------|-----------|
| Tier 1 (fully supported) | Linux x86_64/ARM64, macOS x86_64/ARM64, Windows x86_64 |
| Tier 2 (cross-compiled) | Windows ARM64, FreeBSD x86_64 |
| Tier 3 (bare-metal) | ARM Cortex-M, RISC-V, x86 32-bit |

---

## Related Files

- Architecture overview: `doc/07_guide/architecture.md`
- Compiler architecture: `doc/07_guide/architecture/compiler_architecture.md`
- File structure: `doc/04_architecture/file_class_structure.md`
- LLM dashboard web login operator guide: `doc/07_guide/tooling/llm_dashboard_web_login.md`
- Assistant/dashboard architecture slice: `doc/04_architecture/kairos_like_simple_mcp_llm_dashboard.md`
