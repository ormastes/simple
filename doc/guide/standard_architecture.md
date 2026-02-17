# Simple Standard Architecture Guide

> Clean, maintainable, testable architecture for Simple applications.
>
> Based on Clean Architecture / Hexagonal (Ports & Adapters) / Onion Architecture principles,
> extended with MDSoC (Multi-Dimensional Separation of Concerns).

**Version:** 1.0
**Last Updated:** 2026-02-17

---

## Table of Contents

1. [Core Principles](#1-core-principles)
2. [Architecture Overview](#2-architecture-overview)
3. [The Three Layers](#3-the-three-layers)
4. [The Dimension System](#4-the-dimension-system)
5. [Dependency Rules](#5-dependency-rules)
6. [Directory Structure](#6-directory-structure)
7. [Ports and Adapters](#7-ports-and-adapters)
8. [Transform Layer](#8-transform-layer)
9. [Testing Strategy](#9-testing-strategy)
10. [Common Patterns](#10-common-patterns)
11. [Anti-Patterns to Avoid](#11-anti-patterns-to-avoid)
12. [Migration Guide](#12-migration-guide)
13. [Decision Framework](#13-decision-framework)

---

## 1. Core Principles

### 1.1 The Central Rule: Dependencies Point Inward

```
┌─────────────────────────────────────────┐
│          UI / Controllers               │  ← Volatile (changes often)
│         (Web, CLI, Desktop)             │
└──────────────────┬──────────────────────┘
                   │ depends on
                   ↓
┌─────────────────────────────────────────┐
│        Application / Use Cases          │  ← Orchestration
│      (Business Logic Coordination)      │
└──────────────────┬──────────────────────┘
                   │ depends on
                   ↓
┌─────────────────────────────────────────┐
│      Domain / Entities / Policy         │  ← Stable (core logic)
│    (Business Rules, Invariants)         │
└─────────────────────────────────────────┘

Dependencies flow INWARD (toward policy)
Control flow may go OUTWARD (via ports)
```

**Key insight:** Source-code dependencies ≠ runtime control flow.

- **Source-code dependency:** What you `import` / `use` (compile-time)
- **Runtime control flow:** What calls what (execution-time)

**Rule:** Inner layers NEVER import outer layers. Outer layers import inner interfaces.

### 1.2 Separation of Concerns: Why It Matters

**Problem:** Most systems have TWO volatile edges:
- **UI:** User interface, rendering, input handling, device APIs
- **Infrastructure:** Database, network, file system, external services

Both leak complexity inward if not isolated.

**Solution:** Keep core policy (business logic) independent of both.

### 1.3 The Eight Principles

1. **Policy is stable, mechanisms are volatile**
   - Domain + use-cases = policy
   - UI + DB + frameworks = mechanisms

2. **Dependency Inversion at every IO boundary**
   - Core defines interfaces (ports)
   - Edge implements them (adapters)

3. **One-direction dependency graph (no cycles)**
   - Modules form a DAG
   - Circular dependencies = architecture violation

4. **Explicit boundaries, explicit mapping**
   - Map at boundaries (DTO ↔ domain ↔ persistence)
   - Don't share models across layers

5. **Keep IO at the edges**
   - Core has no network, filesystem, DB calls
   - Core asks via ports

6. **Thin adapters**
   - Adapters translate and delegate
   - No business rules in adapters

7. **Composition root is the only "global knowledge"**
   - Only wiring layer imports both core and adapters

8. **Test strategy aligns with boundaries**
   - Unit-test core without infrastructure
   - Integration-test adapters
   - E2E tests for critical flows

---

## 2. Architecture Overview

### 2.1 Conceptual Model

```
┌────────────────────────────────────────────────┐
│                 ADAPTERS (IN)                  │
│  HTTP Controllers │ GraphQL │ CLI │ UI Events  │
└───────────────────┬────────────────────────────┘
                    │
                    ↓
┌────────────────────────────────────────────────┐
│           APPLICATION LAYER (Use Cases)        │
│  ┌──────────────────────────────────────────┐  │
│  │  Use Case  → Ports (Interfaces)          │  │
│  │  - Repository Port                       │  │
│  │  - Message Bus Port                      │  │
│  │  - Payment Gateway Port                  │  │
│  │  - Clock Port                            │  │
│  └──────────────────────────────────────────┘  │
└───────────────────┬────────────────────────────┘
                    │
                    ↓
┌────────────────────────────────────────────────┐
│           DOMAIN LAYER (Entities)              │
│  Entities │ Value Objects │ Domain Services    │
│  - Pure logic, no framework dependencies       │
└────────────────────────────────────────────────┘
                    ↑
                    │ implements
                    │
┌────────────────────────────────────────────────┐
│               ADAPTERS (OUT)                   │
│  SQL Repos │ REST APIs │ Message Queues │ FS   │
└────────────────────────────────────────────────┘
```

### 2.2 Layer Responsibilities

| Layer | Responsibility | Dependencies |
|-------|---------------|--------------|
| **Domain** | Business rules, invariants, entities | None (pure logic) |
| **Application** | Use cases, orchestration, ports | Domain |
| **Adapters (In)** | Presentation, input handling | Application |
| **Adapters (Out)** | Persistence, external services | Application (ports) |
| **Composition** | Wiring, DI container | All layers |

### 2.3 Simple's Extension: Multi-Dimensional Separation

Simple adds **dimensions** on top of layers:

- **Feature dimension:** Vertical slices (UI + App logic per feature)
- **Entity dimension:** Horizontal slices (Domain entities by taxonomy)
- **Transform dimension:** Bridges feature ↔ entity mismatch

**Why?** Real systems need multiple decompositions simultaneously.

---

## 3. The Three Layers

### 3.1 Layer 1: Domain (Entity Layer)

**Location:** `src/entity/`

**Purpose:** Encapsulate core business logic, invariants, and domain rules.

**Characteristics:**
- ✅ Pure functions and value objects
- ✅ No dependencies on UI, DB, or frameworks
- ✅ Testable without any infrastructure
- ✅ Stable (changes less frequently than features)

**Example: `src/entity/Order/Order.spl`**

```simple
struct Order:
    """
    Domain entity: Order aggregate root.
    Encapsulates order lifecycle and invariants.
    """
    id: text
    customer_id: text
    lines: [OrderLine]
    status: OrderStatus
    created_at: text
    total: f64

    fn add_line(line: OrderLine):
        """Add line item and recalculate total."""
        if self.status != OrderStatus.draft():
            panic("Cannot modify confirmed order")
        self.lines.append(line)
        self.recalculate_total()

    fn confirm():
        """Confirm order (domain rule: must have at least one line)."""
        if self.lines.len() == 0:
            panic("Cannot confirm empty order")
        self.status = OrderStatus.confirmed()

    fn cancel():
        """Cancel order (domain rule: cannot cancel shipped orders)."""
        if self.status == OrderStatus.shipped():
            panic("Cannot cancel shipped order")
        self.status = OrderStatus.cancelled()

    me recalculate_total():
        """Recalculate order total from line items."""
        var sum = 0.0
        for line in self.lines:
            sum = sum + line.total_price()
        self.total = sum

struct OrderLine:
    product_id: text
    quantity: i64
    unit_price: f64

    fn total_price() -> f64:
        self.unit_price * self.quantity

enum OrderStatus:
    Draft
    Confirmed
    Shipped
    Cancelled

    static fn draft() -> OrderStatus:
        OrderStatus.Draft

    static fn confirmed() -> OrderStatus:
        OrderStatus.Confirmed

    static fn shipped() -> OrderStatus:
        OrderStatus.Shipped

    static fn cancelled() -> OrderStatus:
        OrderStatus.Cancelled
```

**Domain Layer Rules:**
- ❌ NO imports from `feature/`, `adapters/`, or `app/io/`
- ❌ NO framework annotations (no ORM, no HTTP, no JSON)
- ❌ NO database queries or network calls
- ✅ CAN import other domain entities
- ✅ CAN import `shared/` utilities (Result, Option, etc.)

### 3.2 Layer 2: Application (Use Case Layer)

**Location:** `src/feature/*/app/`

**Purpose:** Orchestrate domain logic to accomplish user goals.

**Characteristics:**
- ✅ One use-case class/function per user intention
- ✅ Defines **ports** (interfaces) for IO needs
- ✅ Calls domain entities to enforce business rules
- ✅ Depends on domain + transform, not on adapters

**Example: `src/feature/OrderManagement/app/PlaceOrderUseCase.spl`**

```simple
from transform/feature/OrderManagement/entity_view import Order, OrderLine, Customer
from shared import Result

# Port definitions (interfaces)
struct OrderRepository:
    """Port: interface for order persistence."""
    save_fn: fn(Order)
    find_by_id_fn: fn(text) -> Order?
    find_by_customer_fn: fn(text) -> [Order]

struct PaymentGateway:
    """Port: interface for payment processing."""
    charge_fn: fn(text, f64) -> Result  # (payment_method_id, amount)

struct InventoryService:
    """Port: interface for inventory checks."""
    check_availability_fn: fn(text, i64) -> bool  # (product_id, quantity)
    reserve_fn: fn(text, i64) -> Result

# Use case implementation
fn place_order(
    customer_id: text,
    items: [dict],
    payment_method: text,
    order_repo: OrderRepository,
    payment_gateway: PaymentGateway,
    inventory: InventoryService
) -> Result:
    """
    @tag:api
    Place order use case: validate → reserve inventory → charge payment → save order.
    """
    # 1. Validate customer
    val customer = fetch_customer(customer_id)
    if customer == nil:
        return Result.error("Customer not found")

    # 2. Build order lines
    var lines = []
    for item in items:
        # Check inventory
        val available = inventory.check_availability_fn(item["product_id"], item["quantity"])
        if not available:
            return Result.error("Product {item["product_id"]} not available")

        lines.append(OrderLine(
            product_id: item["product_id"],
            quantity: item["quantity"],
            unit_price: item["price"]
        ))

    # 3. Create order (domain entity)
    var order = Order(
        id: generate_order_id(),
        customer_id: customer_id,
        lines: lines,
        status: OrderStatus.draft(),
        created_at: now(),
        total: 0.0
    )
    order.confirm()  # Domain rule: validates non-empty, sets status

    # 4. Reserve inventory
    for line in lines:
        val reserve_result = inventory.reserve_fn(line.product_id, line.quantity)
        if reserve_result.is_error():
            return Result.error("Failed to reserve inventory: {reserve_result.error()}")

    # 5. Process payment
    val payment_result = payment_gateway.charge_fn(payment_method, order.total)
    if payment_result.is_error():
        # Rollback inventory reservation (compensation)
        rollback_inventory(lines, inventory)
        return Result.error("Payment failed: {payment_result.error()}")

    # 6. Save order
    order_repo.save_fn(order)

    Result.ok(order.id)

fn fetch_customer(id: text) -> Customer?:
    pass_todo  # Injected port

fn generate_order_id() -> text:
    pass_todo  # Clock port

fn now() -> text:
    pass_todo  # Clock port

fn rollback_inventory(lines: [OrderLine], inventory: InventoryService):
    for line in lines:
        inventory.unreserve_fn(line.product_id, line.quantity)
```

**Application Layer Rules:**
- ✅ Orchestrate domain logic
- ✅ Define ports (interfaces) for IO
- ✅ Import from `transform/` (not directly from `entity/`)
- ❌ NO direct database or network calls
- ❌ NO business rules (delegate to domain)

### 3.3 Layer 3: UI / Presentation

**Location:** `src/feature/*/ui/`

**Purpose:** Handle user input, rendering, and presentation logic.

**Characteristics:**
- ✅ Framework-specific (web, desktop, CLI)
- ✅ Calls application use-cases
- ✅ Maps DTOs ↔ view models
- ✅ Handles auth context, validation (format only)

**Example: `src/feature/OrderManagement/ui/PlaceOrderController.spl`**

```simple
from feature/OrderManagement/app import place_order, OrderRepository, PaymentGateway, InventoryService
from adapters/http import HttpRequest, HttpResponse
from adapters/persistence import SqlOrderRepository
from adapters/payment import StripePaymentGateway
from adapters/inventory import InventoryServiceImpl

fn handle_place_order(req: HttpRequest) -> HttpResponse:
    """
    HTTP controller: handle POST /orders
    """
    # 1. Parse request (DTO)
    val body = req.json_body()
    val customer_id = body["customer_id"]
    val items = body["items"]
    val payment_method = body["payment_method"]

    # 2. Validate input (format only, not business rules)
    if customer_id == nil or items == nil or items.len() == 0:
        return HttpResponse(status: 400, body: {"error": "Invalid request"})

    # 3. Build ports (DI)
    val order_repo = OrderRepository(
        save_fn: SqlOrderRepository.save,
        find_by_id_fn: SqlOrderRepository.find_by_id,
        find_by_customer_fn: SqlOrderRepository.find_by_customer
    )
    val payment_gateway = PaymentGateway(
        charge_fn: StripePaymentGateway.charge
    )
    val inventory = InventoryService(
        check_availability_fn: InventoryServiceImpl.check_availability,
        reserve_fn: InventoryServiceImpl.reserve
    )

    # 4. Call use case
    val result = place_order(
        customer_id,
        items,
        payment_method,
        order_repo,
        payment_gateway,
        inventory
    )

    # 5. Map result to response
    if result.is_error():
        return HttpResponse(status: 400, body: {"error": result.error()})

    HttpResponse(status: 201, body: {"order_id": result.unwrap()})
```

**UI Layer Rules:**
- ✅ Handle HTTP/UI-specific concerns
- ✅ Map request/response DTOs
- ✅ Inject ports (manual or via DI container)
- ❌ NO business logic (delegate to use-cases)
- ❌ NO direct domain entity manipulation

---

## 4. The Dimension System

### 4.1 Feature Dimension (Vertical Slices)

**Purpose:** Group UI + Application logic by user-facing feature.

**Structure:**
```
src/feature/
  OrderManagement/
    ui/
      PlaceOrderController.spl
      OrderHistoryView.spl
    app/
      PlaceOrderUseCase.spl
      CancelOrderUseCase.spl
    __init__.spl

  UserProfile/
    ui/
      ProfileView.spl
    app/
      UpdateProfileUseCase.spl
    __init__.spl
```

**Benefits:**
- ✅ Easy to add/remove features
- ✅ Teams can work on features independently
- ✅ Clear feature boundaries

### 4.2 Entity Dimension (Horizontal Slices)

**Purpose:** Group domain entities by taxonomy/domain model.

**Structure:**
```
src/entity/
  Order/
    Order.spl
    OrderLine.spl
    OrderStatus.spl
    __init__.spl

  Product/
    Product.spl
    SKU.spl
    Pricing.spl
    __init__.spl

  Customer/
    Customer.spl
    Address.spl
    __init__.spl
```

**Benefits:**
- ✅ Domain model is coherent and stable
- ✅ Easy to reason about business rules
- ✅ Reusable across features

### 4.3 Transform Dimension (Bridge)

**Purpose:** Reconcile mismatch between Feature and Entity dimensions.

**Structure:**
```
src/transform/
  feature/
    OrderManagement/
      entity_view/
        OrderModel.spl  # Re-exports + adaptations
      __init__.spl
    UserProfile/
      entity_view/
        ProfileModel.spl
      __init__.spl
  __init__.spl
```

**Why needed?** Features need different views of entities:
- Checkout feature needs Order + Product + Customer + Inventory
- Reporting feature needs denormalized read-only projections
- UserProfile feature needs Customer + Address (not Order)

**See:** [dimension_transform_examples.md](dimension_transform_examples.md) for detailed examples.

---

## 5. Dependency Rules

### 5.1 Layer Dependencies (Vertical)

```
UI → Application → Domain
 ↓         ↓
Adapters ←─┘
```

**Rules:**
1. **Domain** depends on: nothing (or only `shared/`)
2. **Application** depends on: Domain, Transform
3. **UI** depends on: Application
4. **Adapters** depend on: Application (port interfaces)

### 5.2 Dimension Dependencies (Horizontal)

```
Feature → Transform → Entity
  ↓
  UI
  App
```

**Rules:**
1. **Feature** can import: `transform/**`, `shared/**`
2. **Feature** CANNOT import: `entity/**` (must go through transform)
3. **Transform** can import: `entity/**`, `shared/**`
4. **Transform** CANNOT import: `feature/**` (would create cycle)
5. **Entity** can import: `entity/**`, `shared/**`
6. **Entity** CANNOT import: `feature/**`, `transform/**`

### 5.3 Enforcing Rules with `__init__.spl`

**File: `src/feature/OrderManagement/__init__.spl`**

```simple
arch {
  dimension = "feature"
  layer = "none"

  imports {
    allow = [
      "shared/**",
      "feature/OrderManagement/**",
      "transform/feature/OrderManagement/**"
    ]
    deny = [
      "entity/**"  # Force use of transform
    ]
  }

  exports {
    expose = [
      "./app/PlaceOrderUseCase",
      "./app/CancelOrderUseCase"
    ]
  }
}
```

**File: `src/entity/Order/__init__.spl`**

```simple
arch {
  dimension = "entity"
  layer = "entity"

  imports {
    allow = [
      "entity/**",
      "shared/**"
    ]
    deny = [
      "feature/**",
      "transform/**",
      "adapters/**"
    ]
  }

  exports {
    expose = [
      "./Order",
      "./OrderLine",
      "./OrderStatus"
    ]
  }
}
```

---

## 6. Directory Structure

### 6.1 Full Project Layout

```
src/
  # Core policy (stable)
  entity/                    # Domain entities (horizontal)
    Order/
      Order.spl
      OrderLine.spl
      __init__.spl
    Product/
      Product.spl
      SKU.spl
      __init__.spl
    Customer/
      Customer.spl
      Address.spl
      __init__.spl
    __init__.spl

  # Features (volatile, vertical slices)
  feature/
    OrderManagement/
      ui/
        PlaceOrderController.spl
        OrderHistoryView.spl
        __init__.spl
      app/
        PlaceOrderUseCase.spl
        CancelOrderUseCase.spl
        __init__.spl
      __init__.spl

    UserProfile/
      ui/
        ProfileView.spl
        __init__.spl
      app/
        UpdateProfileUseCase.spl
        __init__.spl
      __init__.spl

    __init__.spl

  # Bridge layer (feature ↔ entity)
  transform/
    feature/
      OrderManagement/
        entity_view/
          OrderModel.spl
          __init__.spl
        __init__.spl
      UserProfile/
        entity_view/
          ProfileModel.spl
          __init__.spl
        __init__.spl
      __init__.spl
    __init__.spl

  # Edge mechanisms (volatile)
  adapters/
    in/                       # Inbound adapters
      http/
        HttpServer.spl
        Middleware.spl
        __init__.spl
      cli/
        CliApp.spl
        __init__.spl
      __init__.spl

    out/                      # Outbound adapters
      persistence/
        SqlOrderRepository.spl
        SqlProductRepository.spl
        __init__.spl
      payment/
        StripePaymentGateway.spl
        __init__.spl
      messaging/
        KafkaPublisher.spl
        __init__.spl
      __init__.spl

    __init__.spl

  # Shared utilities (stable)
  shared/
    Result.spl
    Option.spl
    Validation.spl
    Clock.spl
    __init__.spl

  # Composition root (wiring)
  main/
    AppStartup.spl            # DI container / manual wiring
    Config.spl
    __init__.spl

test/
  unit/
    entity/                   # Domain tests (no infrastructure)
      Order_spec.spl
    feature/
      OrderManagement/
        PlaceOrderUseCase_spec.spl
  integration/
    adapters/                 # Adapter tests (with real DB/services)
      persistence/
        SqlOrderRepository_spec.spl
  system/                     # E2E tests
    order_flow_spec.spl

config/
  dev.sdn
  prod.sdn

doc/
  architecture/
  guide/
  research/
```

### 6.2 Naming Conventions

| Component | Naming Pattern | Example |
|-----------|---------------|---------|
| Domain entity | `{Entity}.spl` | `Order.spl`, `Customer.spl` |
| Use case | `{Verb}{Entity}UseCase.spl` | `PlaceOrderUseCase.spl` |
| Controller | `{Verb}{Entity}Controller.spl` | `PlaceOrderController.spl` |
| Repository | `{Storage}{Entity}Repository.spl` | `SqlOrderRepository.spl` |
| Port interface | `{Entity}Repository` | `OrderRepository` (struct) |
| Adapter impl | `{Tech}{Entity}{Service}.spl` | `StripePaymentGateway.spl` |
| Transform | `{Entity}Model.spl` | `OrderModel.spl` |

---

## 7. Ports and Adapters

### 7.1 Port Definition (Interface)

**Port:** Interface defined by application layer, implemented by adapters.

**Pattern in Simple:**

```simple
# src/feature/OrderManagement/app/ports.spl

struct OrderRepositoryPort:
    """
    Port: order persistence interface.
    Application defines what it needs; adapters implement it.
    """
    save_fn: fn(Order)
    find_by_id_fn: fn(text) -> Order?
    find_by_customer_fn: fn(text) -> [Order]
    delete_fn: fn(text)

struct PaymentGatewayPort:
    """Port: payment processing interface."""
    charge_fn: fn(text, f64) -> Result
    refund_fn: fn(text, f64) -> Result

struct ClockPort:
    """Port: time abstraction (for testing)."""
    now_fn: fn() -> text
```

### 7.2 Adapter Implementation

**Outbound Adapter:** Implements port, talks to external systems.

**Example: `src/adapters/out/persistence/SqlOrderRepository.spl`**

```simple
from entity/Order import Order, OrderLine
from adapters/out/persistence/database import execute_query, fetch_one, fetch_all

fn save(order: Order):
    """Implement OrderRepositoryPort.save_fn"""
    val sql = "INSERT INTO orders (id, customer_id, status, total, created_at) VALUES (?, ?, ?, ?, ?)"
    execute_query(sql, [order.id, order.customer_id, order.status, order.total, order.created_at])

    # Save lines
    for line in order.lines:
        val line_sql = "INSERT INTO order_lines (order_id, product_id, quantity, unit_price) VALUES (?, ?, ?, ?)"
        execute_query(line_sql, [order.id, line.product_id, line.quantity, line.unit_price])

fn find_by_id(order_id: text) -> Order?:
    """Implement OrderRepositoryPort.find_by_id_fn"""
    val sql = "SELECT * FROM orders WHERE id = ?"
    val row = fetch_one(sql, [order_id])
    if row == nil:
        return nil

    val lines = fetch_order_lines(order_id)

    Order(
        id: row["id"],
        customer_id: row["customer_id"],
        status: row["status"],
        total: row["total"],
        created_at: row["created_at"],
        lines: lines
    )

fn find_by_customer(customer_id: text) -> [Order]:
    """Implement OrderRepositoryPort.find_by_customer_fn"""
    val sql = "SELECT * FROM orders WHERE customer_id = ?"
    val rows = fetch_all(sql, [customer_id])
    var orders = []
    for row in rows:
        orders.append(find_by_id(row["id"]))
    orders

fn delete(order_id: text):
    """Implement OrderRepositoryPort.delete_fn"""
    execute_query("DELETE FROM order_lines WHERE order_id = ?", [order_id])
    execute_query("DELETE FROM orders WHERE id = ?", [order_id])

fn fetch_order_lines(order_id: text) -> [OrderLine]:
    val sql = "SELECT * FROM order_lines WHERE order_id = ?"
    val rows = fetch_all(sql, [order_id])
    var lines = []
    for row in rows:
        lines.append(OrderLine(
            product_id: row["product_id"],
            quantity: row["quantity"],
            unit_price: row["unit_price"]
        ))
    lines
```

### 7.3 Inbound Adapter (Controller)

**Example: `src/adapters/in/http/OrderController.spl`**

```simple
from feature/OrderManagement/app import place_order, OrderRepositoryPort
from adapters/out/persistence import SqlOrderRepository
from adapters/http import HttpRequest, HttpResponse

fn handle_post_orders(req: HttpRequest) -> HttpResponse:
    """HTTP POST /orders endpoint"""
    # 1. Parse and validate request
    val body = req.json_body()

    # 2. Wire up ports
    val repo = OrderRepositoryPort(
        save_fn: SqlOrderRepository.save,
        find_by_id_fn: SqlOrderRepository.find_by_id,
        find_by_customer_fn: SqlOrderRepository.find_by_customer,
        delete_fn: SqlOrderRepository.delete
    )

    # 3. Call use case
    val result = place_order(
        customer_id: body["customer_id"],
        items: body["items"],
        payment_method: body["payment_method"],
        repo: repo
    )

    # 4. Map to HTTP response
    if result.is_error():
        return HttpResponse(status: 400, body: {"error": result.error()})

    HttpResponse(status: 201, body: {"order_id": result.unwrap()})
```

### 7.4 Dependency Injection Patterns

**Manual Wiring (Simple, explicit):**

```simple
# src/main/AppStartup.spl

fn start_app():
    # Build adapters
    val order_repo = OrderRepositoryPort(
        save_fn: SqlOrderRepository.save,
        find_by_id_fn: SqlOrderRepository.find_by_id,
        find_by_customer_fn: SqlOrderRepository.find_by_customer,
        delete_fn: SqlOrderRepository.delete
    )

    val payment_gateway = PaymentGatewayPort(
        charge_fn: StripePaymentGateway.charge,
        refund_fn: StripePaymentGateway.refund
    )

    # Start HTTP server with dependencies
    start_http_server(order_repo, payment_gateway)
```

**DI Container (Future):**

```simple
# Potential future Simple DI container syntax
container AppContainer:
    bind OrderRepositoryPort to SqlOrderRepository
    bind PaymentGatewayPort to StripePaymentGateway
    bind ClockPort to SystemClock

    singleton DatabaseConnection

fn start_app():
    val container = AppContainer.build()
    val server = container.resolve(HttpServer)
    server.start()
```

---

## 8. Transform Layer

The Transform dimension bridges the feature and entity dimensions without creating direct cross-dimension imports.

See [dimension_transform_examples.md](dimension_transform_examples.md) for comprehensive examples.

### 8.1 When to Use Transform

**Use Transform when:**
- ✅ Feature needs subset of entity fields
- ✅ Feature uses different terminology than domain
- ✅ Feature needs denormalized view (aggregating multiple entities)
- ✅ Feature needs read-only projection
- ✅ Sensitive fields must be hidden from a feature

**Don't use Transform when:**
- ❌ Entity is already a 1:1 match for the feature (re-export directly)
- ❌ Trying to bypass architectural rules (never allowed)

### 8.2 Transform Patterns

| Pattern | When | Example |
|---------|------|---------|
| **Re-export** | Entity is already feature-friendly | `reexport entity/Order as Order` |
| **Adapter** | Need to rename or reshape | `struct UserPayment` from `Transaction` |
| **Aggregation** | Combine multiple entities | `struct CheckoutContext` |
| **Projection** | Read-only denormalized view | `struct SalesReportRow` |
| **Computed** | Need derived fields (e.g., totals, formatting) | `struct InvoiceSummary` with computed `total` |

### 8.3 Directory Structure

Transform mirrors the destination dimension's structure:

```
transform/
  feature/
    <FeatureName>/
      __init__.spl          ← transform config (from→to, allow_from)
      entity_view/
        __init__.spl        ← re-export declarations
        <FeatureName>Model.spl  ← adapted structs + factory fns
```

### 8.4 `__init__.spl` Transform Config

**Global policy** at `src/transform/__init__.spl`:

```simple
arch {
  dimension = "transform"
  layer = "none"

  transform_pairs = [
    { from = "entity", to = "feature" }
  ]

  imports {
    deny = ["feature/**"]   # transform never imports features
  }
}
```

**Per-feature transform** at `src/transform/feature/<Name>/__init__.spl`:

```simple
arch {
  dimension = "transform"
  layer = "none"

  transform {
    from = "entity"
    to   = "feature"
    allow_from = ["entity/Order/**", "entity/Customer/**"]  # whitelist
  }

  imports {
    allow = ["entity/**", "shared/**"]
    deny  = ["feature/**"]
  }

  exports {
    expose = ["./entity_view/**"]
  }
}
```

**Feature declaration** at `src/feature/<Name>/__init__.spl`:

```simple
arch {
  dimension = "feature"
  layer = "none"

  uses_transform = "transform/feature/<Name>"

  imports {
    allow = ["shared/**", "feature/<Name>/**", "transform/feature/<Name>/**"]
    deny  = ["entity/**"]     # never import entity directly
  }
}
```

### 8.5 Re-export Rule

Only a directory with `dimension = "transform"` and an explicit `transform { from, to }` declaration may re-export types from another dimension:

```simple
# ✅ ALLOWED — inside transform/feature/Auth/entity_view/
reexport entity/Identity/User as User

# ❌ FORBIDDEN — inside feature/Auth/app/ (not a transform module)
reexport entity/Identity/User as User  # compile error
```

### 8.6 Example: Minimal Transform

`src/transform/feature/Checkout/entity_view/CheckoutModel.spl`:

```simple
from entity/Order/Order import Order
from entity/Customer/Customer import Customer
from entity/Product/Product import Product

struct CheckoutContext:
    """
    Feature-friendly aggregation for the checkout flow.
    """
    customer_name: text
    customer_email: text
    items: [CheckoutItem]
    subtotal_cents: i64

struct CheckoutItem:
    product_id: text
    name: text
    quantity: i64
    unit_price_cents: i64

fn build_checkout_context(
    customer: Customer,
    order: Order,
    products: [Product]
) -> CheckoutContext:
    val items = order.lines.map(\line:
        val product = products.find(\p: p.id == line.product_id) ?? Product.unknown()
        CheckoutItem(
            product_id: line.product_id,
            name: product.name,
            quantity: line.quantity,
            unit_price_cents: line.unit_price_cents
        )
    )
    CheckoutContext(
        customer_name: customer.full_name,
        customer_email: customer.email,
        items: items,
        subtotal_cents: order.subtotal_cents
    )
```

---

## 9. Testing Strategy

### 9.1 Test Pyramid

```
      E2E (Few)           ← Full system, critical flows
     /         \
  Integration (Some)      ← Adapters + real DB/services
  /               \
Unit (Many)        ← Domain + use-cases, no infrastructure
```

### 9.2 Domain Tests (Unit)

**Test:** Domain entities without any infrastructure.

**Example: `test/unit/entity/Order_spec.spl`**

```simple
from entity/Order import Order, OrderLine, OrderStatus

describe "Order entity":
    it "calculates total from line items":
        var order = Order(
            id: "1",
            customer_id: "c1",
            lines: [],
            status: OrderStatus.draft(),
            created_at: "2026-01-01",
            total: 0.0
        )

        order.add_line(OrderLine(product_id: "p1", quantity: 2, unit_price: 10.0))
        order.add_line(OrderLine(product_id: "p2", quantity: 1, unit_price: 5.0))

        expect(order.total).to_equal(25.0)

    it "prevents modification after confirmation":
        var order = Order(
            id: "1",
            customer_id: "c1",
            lines: [OrderLine(product_id: "p1", quantity: 1, unit_price: 10.0)],
            status: OrderStatus.draft(),
            created_at: "2026-01-01",
            total: 10.0
        )

        order.confirm()

        # Should panic
        val error = try_add_line(order, OrderLine(product_id: "p2", quantity: 1, unit_price: 5.0))
        expect(error).to_contain("Cannot modify confirmed order")

fn try_add_line(order: Order, line: OrderLine) -> text:
    # Capture panic as error string
    pass_todo
```

### 9.3 Use Case Tests (Unit with Mocks)

**Test:** Use cases with mock ports.

**Example: `test/unit/feature/OrderManagement/PlaceOrderUseCase_spec.spl`**

```simple
from feature/OrderManagement/app import place_order, OrderRepositoryPort, PaymentGatewayPort
from entity/Order import Order
from shared import Result

describe "PlaceOrderUseCase":
    it "places order successfully":
        # Mock repository
        var saved_order = nil
        val mock_repo = OrderRepositoryPort(
            save_fn: fn(order): saved_order = order,
            find_by_id_fn: fn(id): nil,
            find_by_customer_fn: fn(id): [],
            delete_fn: fn(id): pass_do_nothing
        )

        # Mock payment gateway
        var charged_amount = 0.0
        val mock_payment = PaymentGatewayPort(
            charge_fn: fn(method, amount):
                charged_amount = amount
                Result.ok(),
            refund_fn: fn(txn, amount): Result.ok()
        )

        # Execute use case
        val result = place_order(
            customer_id: "c1",
            items: [{"product_id": "p1", "quantity": 2, "price": 10.0}],
            payment_method: "pm_123",
            repo: mock_repo,
            payment: mock_payment
        )

        # Assert
        expect(result.is_ok()).to_equal(true)
        expect(saved_order).to_not_be_nil()
        expect(charged_amount).to_equal(20.0)

    it "rolls back on payment failure":
        var save_called = false
        val mock_repo = OrderRepositoryPort(
            save_fn: fn(order): save_called = true,
            find_by_id_fn: fn(id): nil,
            find_by_customer_fn: fn(id): [],
            delete_fn: fn(id): pass_do_nothing
        )

        val mock_payment = PaymentGatewayPort(
            charge_fn: fn(method, amount): Result.error("Payment declined"),
            refund_fn: fn(txn, amount): Result.ok()
        )

        val result = place_order(
            customer_id: "c1",
            items: [{"product_id": "p1", "quantity": 1, "price": 10.0}],
            payment_method: "pm_123",
            repo: mock_repo,
            payment: mock_payment
        )

        expect(result.is_error()).to_equal(true)
        expect(save_called).to_equal(false)  # Should NOT save on failure
```

### 9.4 Adapter Tests (Integration)

**Test:** Adapters with real infrastructure (DB, APIs).

**Example: `test/integration/adapters/persistence/SqlOrderRepository_spec.spl`**

```simple
from adapters/out/persistence/SqlOrderRepository import save, find_by_id
from entity/Order import Order, OrderLine, OrderStatus
from test_helpers import setup_test_db, teardown_test_db

describe "SqlOrderRepository":
    before_each:
        setup_test_db()

    after_each:
        teardown_test_db()

    it "saves and retrieves order":
        val order = Order(
            id: "order_1",
            customer_id: "c1",
            lines: [
                OrderLine(product_id: "p1", quantity: 2, unit_price: 10.0)
            ],
            status: OrderStatus.confirmed(),
            created_at: "2026-01-01",
            total: 20.0
        )

        save(order)

        val retrieved = find_by_id("order_1")
        expect(retrieved).to_not_be_nil()
        expect(retrieved.customer_id).to_equal("c1")
        expect(retrieved.lines.len()).to_equal(1)
        expect(retrieved.total).to_equal(20.0)
```

### 9.5 E2E Tests (System)

**Test:** Full system via HTTP/CLI interface.

**Example: `test/system/order_flow_spec.spl`**

```simple
from test_helpers import start_test_server, stop_test_server, http_post, http_get

describe "Order flow (E2E)":
    before_each:
        start_test_server()

    after_each:
        stop_test_server()

    it "places order end-to-end":
        # POST /orders
        val response = http_post("/orders", {
            "customer_id": "c1",
            "items": [
                {"product_id": "p1", "quantity": 2, "price": 10.0}
            ],
            "payment_method": "pm_123"
        })

        expect(response.status).to_equal(201)
        val order_id = response.body["order_id"]

        # GET /orders/{id}
        val get_response = http_get("/orders/{order_id}")
        expect(get_response.status).to_equal(200)
        expect(get_response.body["customer_id"]).to_equal("c1")
        expect(get_response.body["status"]).to_equal("confirmed")
```

---

## 10. Common Patterns

### 10.1 Query Object Pattern

**Use case:** Complex queries with many optional filters.

```simple
struct OrderQuery:
    customer_id: text?
    status: OrderStatus?
    start_date: text?
    end_date: text?
    min_total: f64?
    max_total: f64?

    fn matches(order: Order) -> bool:
        if self.customer_id? and order.customer_id != self.customer_id:
            return false
        if self.status? and order.status != self.status:
            return false
        # ... more filters
        true

# Port
struct OrderRepositoryPort:
    find_by_query_fn: fn(OrderQuery) -> [Order]

# Use case
fn search_orders(query: OrderQuery, repo: OrderRepositoryPort) -> [Order]:
    repo.find_by_query_fn(query)
```

### 10.2 Specification Pattern

**Use case:** Complex business rules that need to be reusable.

```simple
struct OrderSpecification:
    check_fn: fn(Order) -> bool

fn is_eligible_for_discount() -> OrderSpecification:
    OrderSpecification(
        check_fn: fn(order):
            order.total > 100.0 and order.customer.is_premium()
    )

fn is_high_value() -> OrderSpecification:
    OrderSpecification(
        check_fn: fn(order):
            order.total > 1000.0
    )

# Usage in use case
fn apply_discount_if_eligible(order: Order) -> Order:
    val spec = is_eligible_for_discount()
    if spec.check_fn(order):
        order.apply_discount(0.1)  # 10% discount
    order
```

### 10.3 Repository Pattern (Full)

```simple
struct Repository<T>:
    """Generic repository port"""
    save_fn: fn(T)
    find_by_id_fn: fn(text) -> T?
    find_all_fn: fn() -> [T]
    delete_fn: fn(text)
    query_fn: fn(dict) -> [T]  # Generic query with filters

# Specialized
type OrderRepository = Repository<Order>
type ProductRepository = Repository<Product>
```

### 10.4 Unit of Work Pattern

**Use case:** Transactional consistency across multiple repositories.

```simple
struct UnitOfWork:
    """Port: transactional boundary"""
    begin_fn: fn()
    commit_fn: fn() -> Result
    rollback_fn: fn()
    order_repo: OrderRepositoryPort
    inventory_repo: InventoryRepositoryPort

fn place_order_transactional(
    customer_id: text,
    items: [dict],
    uow: UnitOfWork
) -> Result:
    uow.begin_fn()

    # Multiple operations
    val order = create_order(customer_id, items)
    uow.order_repo.save_fn(order)

    for item in items:
        val reserve_result = uow.inventory_repo.reserve_fn(item["product_id"], item["quantity"])
        if reserve_result.is_error():
            uow.rollback_fn()
            return reserve_result

    val commit_result = uow.commit_fn()
    if commit_result.is_error():
        uow.rollback_fn()
        return commit_result

    Result.ok(order.id)
```

---

## 11. Anti-Patterns to Avoid

### 11.1 ❌ Anemic Domain Model

**Problem:** Domain entities are just data bags, all logic in services.

```simple
# BAD
struct Order:
    id: text
    customer_id: text
    lines: [OrderLine]
    total: f64

# All logic in service
fn OrderService.calculate_total(order: Order) -> f64:
    var sum = 0.0
    for line in order.lines:
        sum = sum + (line.quantity * line.unit_price)
    sum
```

**Fix:** Move behavior into entities.

```simple
# GOOD
struct Order:
    id: text
    customer_id: text
    lines: [OrderLine]
    total: f64

    fn calculate_total() -> f64:
        var sum = 0.0
        for line in self.lines:
            sum = sum + line.total_price()
        sum

    fn add_line(line: OrderLine):
        self.lines.append(line)
        self.total = self.calculate_total()
```

### 11.2 ❌ God Object / Fat Controller

**Problem:** Controller contains business logic.

```simple
# BAD: controller has business rules
fn handle_place_order(req: HttpRequest) -> HttpResponse:
    val body = req.json_body()

    # Validation logic in controller ❌
    if body["items"].len() == 0:
        return HttpResponse(status: 400, body: {"error": "Empty order"})

    # Business logic in controller ❌
    var total = 0.0
    for item in body["items"]:
        total = total + (item["quantity"] * item["price"])

    if total > 1000:
        total = total * 0.9  # Apply discount ❌

    # Persistence logic in controller ❌
    execute_sql("INSERT INTO orders ...")

    HttpResponse(status: 201)
```

**Fix:** Move logic to use case and domain.

```simple
# GOOD: controller delegates
fn handle_place_order(req: HttpRequest) -> HttpResponse:
    val body = req.json_body()

    val result = place_order_use_case(
        body["customer_id"],
        body["items"],
        body["payment_method"]
    )

    if result.is_error():
        return HttpResponse(status: 400, body: {"error": result.error()})

    HttpResponse(status: 201, body: {"order_id": result.unwrap()})
```

### 11.3 ❌ Leaky Abstractions (ORM/DTO Leak)

**Problem:** Passing ORM entities or DTOs directly into domain.

```simple
# BAD: ORM entity in domain
from database.orm import OrderEntity  # ❌

struct PlaceOrderUseCase:
    fn execute(order_entity: OrderEntity):  # ❌ ORM type in use case
        order_entity.status = "confirmed"
        order_entity.save()  # ❌ ORM method in use case
```

**Fix:** Map at boundaries.

```simple
# GOOD: map at adapter boundary
fn SqlOrderRepository.save(order: Order):
    # Map domain → ORM
    val entity = OrderEntity.from_domain(order)
    entity.save()

fn SqlOrderRepository.find_by_id(id: text) -> Order?:
    val entity = OrderEntity.find(id)
    if entity == nil:
        return nil
    # Map ORM → domain
    entity.to_domain()
```

### 11.4 ❌ Circular Dependencies

**Problem:** Feature imports entity, entity imports feature.

```simple
# BAD: circular dependency
# src/entity/Order/Order.spl
from feature/OrderManagement/app import send_notification  # ❌

struct Order:
    fn confirm():
        self.status = OrderStatus.confirmed()
        send_notification(self)  # ❌ Entity calls feature
```

**Fix:** Use ports (dependency inversion).

```simple
# GOOD: entity defines event, feature subscribes
# src/entity/Order/Order.spl
struct OrderConfirmedEvent:
    order_id: text
    customer_id: text
    timestamp: text

struct Order:
    fn confirm(event_bus: EventBus):
        self.status = OrderStatus.confirmed()
        event_bus.publish(OrderConfirmedEvent(
            order_id: self.id,
            customer_id: self.customer_id,
            timestamp: now()
        ))

# src/feature/Notifications/app/OrderEventHandler.spl
fn on_order_confirmed(event: OrderConfirmedEvent):
    send_notification(event.customer_id, "Order confirmed")
```

### 11.5 ❌ Business Logic in Adapters

**Problem:** Adapter contains decision-making logic.

```simple
# BAD: adapter has business rules
fn SqlOrderRepository.save(order: Order):
    # Business rule in adapter ❌
    if order.total > 1000:
        order.apply_vip_discount()

    execute_sql("INSERT INTO orders ...")
```

**Fix:** Adapters only translate, never decide.

```simple
# GOOD: adapter just persists
fn SqlOrderRepository.save(order: Order):
    val sql = "INSERT INTO orders (id, customer_id, total, status) VALUES (?, ?, ?, ?)"
    execute_query(sql, [order.id, order.customer_id, order.total, order.status])
```

---

## 12. Migration Guide

### 12.1 From Monolith to Layered Architecture

**Step 1:** Identify and extract domain entities.

```
Before:
  src/
    everything.spl  # 5000 lines

After:
  src/
    entity/
      Order.spl
      Product.spl
    app/
      old_logic.spl  # Remaining 4000 lines
```

**Step 2:** Extract use cases from app layer.

**Step 3:** Define ports for IO dependencies.

**Step 4:** Move IO code into adapters.

**Step 5:** Wire everything in composition root.

### 12.2 From Layered to MDSoC

**Step 1:** Identify features (vertical slices).

**Step 2:** Create `feature/` directories.

**Step 3:** Move UI + App code into feature folders.

**Step 4:** Create `transform/` layer for feature → entity bridges.

**Step 5:** Enforce dependency rules with `__init__.spl`.

---

## 13. Decision Framework

### 13.1 Where Does This Code Go?

```
┌──────────────────────────────────────────────────┐
│ Is it a business rule or invariant?              │
│   YES → Domain (entity/)                         │
│   NO  → ↓                                        │
└──────────────────────────────────────────────────┘
                     ↓
┌──────────────────────────────────────────────────┐
│ Does it orchestrate multiple domain objects?     │
│   YES → Application (feature/*/app/)             │
│   NO  → ↓                                        │
└──────────────────────────────────────────────────┘
                     ↓
┌──────────────────────────────────────────────────┐
│ Does it handle HTTP/UI/CLI concerns?             │
│   YES → UI (feature/*/ui/ or adapters/in/)       │
│   NO  → ↓                                        │
└──────────────────────────────────────────────────┘
                     ↓
┌──────────────────────────────────────────────────┐
│ Does it talk to DB/external services?            │
│   YES → Adapter (adapters/out/)                  │
│   NO  → ↓                                        │
└──────────────────────────────────────────────────┘
                     ↓
┌──────────────────────────────────────────────────┐
│ Is it a utility used everywhere?                 │
│   YES → Shared (shared/)                         │
└──────────────────────────────────────────────────┘
```

### 13.2 When to Create a New Feature?

**Create new feature when:**
- ✅ It's a distinct user-facing capability
- ✅ It can be developed independently
- ✅ It has its own UI + use cases

**Don't create feature when:**
- ❌ It's just a single function
- ❌ It's purely a domain concept (belongs in entity/)
- ❌ It's infrastructure (belongs in adapters/)

### 13.3 When to Use Transform vs Direct Import?

**Use Transform when:**
- ✅ Feature needs subset of entity
- ✅ Feature uses different terminology
- ✅ Feature needs aggregation of multiple entities
- ✅ You want to enforce clean boundaries

**Direct import OK when:**
- ✅ Feature = Entity (1:1 match, rare)
- ✅ Prototyping (but refactor later)

---

## Summary

**Simple Standard Architecture:**
- **3 Layers:** Domain (stable policy) ← Application (use cases) ← UI (volatile)
- **3 Dimensions:** Feature (vertical) + Entity (horizontal) + Transform (bridge)
- **Dependency Rule:** Source-code dependencies point inward (toward policy)
- **Ports & Adapters:** Core defines interfaces, edges implement them
- **Testing:** Unit (domain), Integration (adapters), E2E (critical flows)

**Key Benefits:**
- ✅ Core business logic is testable without infrastructure
- ✅ UI and DB are replaceable
- ✅ Features can be added/removed independently
- ✅ Domain model stays coherent and stable

**Next Steps:**
1. Read [dimension_transform_examples.md](dimension_transform_examples.md)
2. Review [mdsoc_design.md](../research/mdsoc_design.md)
3. Start with one feature, apply architecture incrementally
4. Use `__init__.spl` to enforce rules

---

## References

- **Clean Architecture:** https://blog.cleancoder.com/uncle-bob/2012/08/13/the-clean-architecture.html
- **Hexagonal Architecture:** Alistair Cockburn, "Hexagonal Architecture" (2005)
- **Onion Architecture:** Jeffrey Palermo (2008)
- **MDSoC / Hyper/J:** https://cacm.acm.org/research/using-multidimensional-separation-of-concerns-to-reshape-evolving-software/
- **DDD (Domain-Driven Design):** Eric Evans, "Domain-Driven Design" (2003)
