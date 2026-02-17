# Dimension Transform Examples for Simple MDSoC

This document provides concrete examples of dimension transforms in Simple's MDSoC architecture.

---

## Overview

**Dimension transforms** bridge the gap between:
- **Feature dimension** (vertical slices: UI + Business logic grouped by feature)
- **Entity dimension** (horizontal slice: Domain entities grouped by taxonomy)

Transform provides feature-friendly views without allowing direct `feature → entity` imports.

---

## Example 1: E-commerce Order Processing

### Entity Dimension (Domain Model)

```
src/entity/
  Order/
    Order.spl         # Core order entity
    OrderLine.spl     # Line items
    OrderStatus.spl   # Status enum
    __init__.spl

  Product/
    Product.spl       # Product catalog entity
    SKU.spl          # Stock keeping unit
    Pricing.spl      # Price rules
    __init__.spl

  Customer/
    Customer.spl      # Customer entity
    Address.spl       # Shipping/billing addresses
    PaymentMethod.spl
    __init__.spl

  Inventory/
    Stock.spl         # Stock levels
    Warehouse.spl     # Warehouse locations
    __init__.spl
```

### Feature Dimension (Use Cases)

```
src/feature/
  Checkout/
    ui/
      CartView.spl
      CheckoutForm.spl
    app/
      CheckoutUseCase.spl
      PaymentProcessor.spl
    __init__.spl

  OrderTracking/
    ui/
      OrderHistoryView.spl
      TrackingView.spl
    app/
      OrderTrackingUseCase.spl
    __init__.spl

  ProductBrowsing/
    ui/
      ProductList.spl
      ProductDetail.spl
    app/
      SearchUseCase.spl
      RecommendationEngine.spl
    __init__.spl
```

### Transform: Checkout Feature View

**File: `src/transform/feature/Checkout/__init__.spl`**

```simple
arch {
  dimension = "transform"
  layer = "none"

  transform {
    from = "entity"
    to = "feature"
    allow_from = [
      "entity/Order/**",
      "entity/Product/**",
      "entity/Customer/**",
      "entity/Inventory/**"
    ]
  }

  imports {
    allow = ["entity/**", "shared/**"]
    deny = ["feature/**"]
  }

  exports {
    expose = ["./entity_view/**"]
  }
}
```

**File: `src/transform/feature/Checkout/entity_view/CheckoutModel.spl`**

```simple
# Re-export only what Checkout feature needs
reexport entity/Order/Order as Order
reexport entity/Order/OrderLine as OrderLine
reexport entity/Product/Product as Product
reexport entity/Product/Pricing as Pricing
reexport entity/Customer/Customer as Customer
reexport entity/Customer/Address as ShippingAddress
reexport entity/Customer/PaymentMethod as PaymentMethod
reexport entity/Inventory/Stock as Stock

# Adaptation: aggregate multiple entities for checkout-specific view
struct CheckoutContext:
    """
    Feature-specific view aggregating multiple entities.
    Checkout doesn't need full entity complexity.
    """
    customer: Customer
    cart_items: [OrderLine]
    shipping: ShippingAddress
    payment: PaymentMethod
    available_stock: [Stock]

    fn total_price() -> f64:
        val sum = 0.0
        for item in self.cart_items:
            val price = Pricing(item.product_id).current_price()
            sum = sum + (price * item.quantity)
        sum

    fn validate_availability() -> Result:
        for item in self.cart_items:
            val stock_level = self.find_stock(item.product_id)
            if stock_level < item.quantity:
                return Result.error("Insufficient stock for {item.product_id}")
        Result.ok()

    fn find_stock(product_id: text) -> i64:
        for s in self.available_stock:
            if s.product_id == product_id:
                return s.quantity
        0
```

**File: `src/feature/Checkout/app/CheckoutUseCase.spl`**

```simple
# Feature imports ONLY from transform, never directly from entity
from transform/feature/Checkout/entity_view import CheckoutContext, Order, Customer
from shared import Result

fn process_checkout(customer_id: text, cart_items: [dict]) -> Result:
    """
    @tag:api
    Process checkout flow: validate → create order → process payment
    """
    # Build checkout context from transform-provided types
    val ctx = CheckoutContext(
        customer: fetch_customer(customer_id),
        cart_items: build_cart(cart_items),
        shipping: fetch_shipping(customer_id),
        payment: fetch_payment(customer_id),
        available_stock: fetch_stock(cart_items)
    )

    # Validate availability
    val validation = ctx.validate_availability()
    if validation.is_error():
        return validation

    # Create order
    val order = Order(
        customer_id: customer_id,
        lines: ctx.cart_items,
        total: ctx.total_price(),
        status: "pending"
    )

    # Process payment (uses PaymentMethod from transform)
    val payment_result = process_payment(ctx.payment, order.total)
    if payment_result.is_error():
        return payment_result

    # Finalize
    order.status = "confirmed"
    save_order(order)

    Result.ok(order.id)

fn fetch_customer(id: text) -> Customer:
    pass_todo  # Port implementation

fn build_cart(items: [dict]) -> [OrderLine]:
    pass_todo  # Port implementation

fn fetch_shipping(customer_id: text) -> ShippingAddress:
    pass_todo  # Port implementation

fn fetch_payment(customer_id: text) -> PaymentMethod:
    pass_todo  # Port implementation

fn fetch_stock(items: [dict]) -> [Stock]:
    pass_todo  # Port implementation

fn process_payment(method: PaymentMethod, amount: f64) -> Result:
    pass_todo  # Port implementation

fn save_order(order: Order):
    pass_todo  # Port implementation
```

---

## Example 2: User Authentication & Authorization

### Entity Dimension

```
src/entity/
  Identity/
    User.spl
    Credential.spl
    Role.spl
    Permission.spl
    __init__.spl

  Session/
    Session.spl
    Token.spl
    RefreshToken.spl
    __init__.spl

  Audit/
    LoginAttempt.spl
    SecurityEvent.spl
    __init__.spl
```

### Transform: Auth Feature View

**File: `src/transform/feature/Auth/entity_view/AuthModel.spl`**

```simple
reexport entity/Identity/User as User
reexport entity/Identity/Credential as Credential
reexport entity/Session/Session as Session
reexport entity/Session/Token as Token

# Adaptation: simplified auth context (feature doesn't need full Permission model)
struct AuthContext:
    """
    Simplified authentication context for Auth feature.
    Hides complex role/permission hierarchy.
    """
    user: User
    session: Session
    token: Token

    fn is_authenticated() -> bool:
        self.session.is_active() and self.token.is_valid()

    fn has_role(role_name: text) -> bool:
        # Delegates to full entity model internally
        self.user.has_role(role_name)

    fn can_access(resource: text) -> bool:
        # Simplified permission check
        self.user.can_access(resource)

# Feature-specific aggregate for login flow
struct LoginRequest:
    username: text
    password: text
    remember_me: bool

struct LoginResponse:
    success: bool
    token: Token?
    error_message: text?
    requires_mfa: bool
```

**File: `src/feature/Auth/app/LoginUseCase.spl`**

```simple
from transform/feature/Auth/entity_view import AuthContext, LoginRequest, LoginResponse, User, Credential, Session, Token
from shared import Result

fn login(request: LoginRequest) -> Result:
    """
    @tag:api
    Authenticate user and create session.
    """
    # Fetch user (through port)
    val user_result = find_user_by_username(request.username)
    if user_result.is_error():
        return log_failed_attempt(request.username, "user_not_found")

    val user = user_result.unwrap()

    # Verify credential
    val cred = fetch_credential(user.id)
    if not verify_password(cred, request.password):
        return log_failed_attempt(request.username, "invalid_password")

    # Check if MFA required
    if user.mfa_enabled:
        return Result.ok(LoginResponse(
            success: false,
            token: nil,
            error_message: nil,
            requires_mfa: true
        ))

    # Create session
    val session = create_session(user)
    val token = generate_token(session, request.remember_me)

    # Build auth context
    val ctx = AuthContext(
        user: user,
        session: session,
        token: token
    )

    # Log success
    log_successful_login(user.id)

    Result.ok(LoginResponse(
        success: true,
        token: token,
        error_message: nil,
        requires_mfa: false
    ))

# Port definitions (implemented by adapters)
fn find_user_by_username(username: text) -> Result:
    pass_todo

fn fetch_credential(user_id: text) -> Credential:
    pass_todo

fn verify_password(cred: Credential, password: text) -> bool:
    pass_todo

fn create_session(user: User) -> Session:
    pass_todo

fn generate_token(session: Session, long_lived: bool) -> Token:
    pass_todo

fn log_failed_attempt(username: text, reason: text) -> Result:
    pass_todo

fn log_successful_login(user_id: text):
    pass_todo
```

---

## Example 3: Reporting Feature (Read-Only Projection)

### Entity Dimension

```
src/entity/
  Sales/
    Invoice.spl
    InvoiceLine.spl
    PaymentRecord.spl
    __init__.spl

  Customer/
    Customer.spl
    CustomerSegment.spl
    __init__.spl
```

### Transform: Reporting Feature View

**File: `src/transform/feature/Reporting/entity_view/ReportingModel.spl`**

```simple
# Reporting needs read-only projections, not full entities
# This is a shape-changing transform (not just re-export)

struct SalesReportRow:
    """
    Denormalized view for reporting.
    Aggregates Invoice + Customer + PaymentRecord.

    NOTE: This is NOT the same as entity/Sales/Invoice.
    This is a read-only projection optimized for reporting queries.
    """
    invoice_id: text
    invoice_date: text
    customer_id: text
    customer_name: text
    customer_segment: text
    total_amount: f64
    payment_status: text
    payment_date: text?

    static fn from_entities(invoice, customer, payment) -> SalesReportRow:
        """
        Adapter: convert entity types to reporting row.
        """
        SalesReportRow(
            invoice_id: invoice.id,
            invoice_date: invoice.created_at,
            customer_id: customer.id,
            customer_name: customer.name,
            customer_segment: customer.segment.name,
            total_amount: invoice.total,
            payment_status: payment.status,
            payment_date: payment.paid_at
        )

struct ReportFilter:
    """
    Feature-specific query filter.
    """
    start_date: text?
    end_date: text?
    customer_segment: text?
    min_amount: f64?
    max_amount: f64?

# Re-export enums needed for filtering
reexport entity/Sales/PaymentStatus as PaymentStatus
reexport entity/Customer/CustomerSegment as CustomerSegment
```

**File: `src/feature/Reporting/app/SalesReportUseCase.spl`**

```simple
from transform/feature/Reporting/entity_view import SalesReportRow, ReportFilter, PaymentStatus
from shared import Result

fn generate_sales_report(filter: ReportFilter) -> Result:
    """
    @tag:api
    Generate sales report with filtering.
    Uses read-only projections from transform.
    """
    # Fetch data through repository port
    val rows = fetch_report_data(filter)

    # Aggregate
    val total = calculate_total(rows)
    val by_segment = group_by_segment(rows)
    val by_status = group_by_status(rows)

    # Return report structure
    Result.ok({
        "rows": rows,
        "total_amount": total,
        "by_segment": by_segment,
        "by_payment_status": by_status,
        "row_count": rows.len()
    })

fn fetch_report_data(filter: ReportFilter) -> [SalesReportRow]:
    """
    Port: implemented by adapter (SQL query, not entity traversal).
    """
    pass_todo

fn calculate_total(rows: [SalesReportRow]) -> f64:
    var sum = 0.0
    for row in rows:
        sum = sum + row.total_amount
    sum

fn group_by_segment(rows: [SalesReportRow]) -> dict:
    var groups = {}
    for row in rows:
        val segment = row.customer_segment
        if not groups.contains(segment):
            groups[segment] = []
        groups[segment].append(row)
    groups

fn group_by_status(rows: [SalesReportRow]) -> dict:
    var groups = {}
    for row in rows:
        val status = row.payment_status
        if not groups.contains(status):
            groups[status] = []
        groups[status].append(row)
    groups
```

---

## Example 4: Transform with Renaming (Terminology Alignment)

Sometimes features use different terminology than the domain model.

**Entity: `src/entity/Finance/Transaction.spl`**

```simple
struct Transaction:
    """Domain model: financial transaction"""
    id: text
    debtor_account: text
    creditor_account: text
    amount: f64
    currency: text
    posting_date: text
```

**Transform: `src/transform/feature/UserDashboard/entity_view/PaymentModel.spl`**

```simple
# Rename for user-facing feature (users see "payments", not "transactions")
reexport entity/Finance/Transaction as Payment

# Adapter: provide user-friendly field names
struct UserPayment:
    """
    User-facing view of a payment.
    Terminology: 'from_account' and 'to_account' instead of 'debtor'/'creditor'.
    """
    payment_id: text
    from_account: text
    to_account: text
    amount: f64
    currency: text
    date: text

    static fn from_transaction(txn) -> UserPayment:
        UserPayment(
            payment_id: txn.id,
            from_account: txn.debtor_account,
            to_account: txn.creditor_account,
            amount: txn.amount,
            currency: txn.currency,
            date: txn.posting_date
        )
```

---

## Example 5: Multi-Entity Aggregation (Complex Transform)

**Scenario:** Notification feature needs data from User, Order, Product, and Inventory.

**Transform: `src/transform/feature/Notifications/entity_view/NotificationModel.spl`**

```simple
reexport entity/Identity/User as User
reexport entity/Order/Order as Order
reexport entity/Product/Product as Product
reexport entity/Inventory/Stock as Stock

struct OrderUpdateNotification:
    """
    Aggregates multiple entities for notification context.
    """
    user_name: text
    user_email: text
    order_id: text
    order_status: text
    product_names: [text]
    estimated_delivery: text?

    static fn build(user: User, order: Order, products: [Product]) -> OrderUpdateNotification:
        var names = []
        for p in products:
            names.append(p.name)

        OrderUpdateNotification(
            user_name: user.full_name,
            user_email: user.email,
            order_id: order.id,
            order_status: order.status,
            product_names: names,
            estimated_delivery: order.estimated_delivery_date
        )

struct StockAlertNotification:
    """
    Low-stock alert for admin users.
    """
    product_id: text
    product_name: text
    current_stock: i64
    threshold: i64
    warehouse_location: text

    static fn build(product: Product, stock: Stock) -> StockAlertNotification:
        StockAlertNotification(
            product_id: product.id,
            product_name: product.name,
            current_stock: stock.quantity,
            threshold: stock.reorder_threshold,
            warehouse_location: stock.warehouse.location
        )
```

---

## Anti-Patterns to Avoid

### ❌ Anti-Pattern 1: Feature imports entity directly

```simple
# src/feature/Checkout/app/CheckoutUseCase.spl

# WRONG - bypasses transform layer
from entity/Order/Order import Order  # ❌ FORBIDDEN

fn process(items):
    val order = Order(...)  # Direct entity construction
```

**Why forbidden:** Breaks architectural boundary, creates tight coupling.

### ❌ Anti-Pattern 2: Transform imports feature (creates cycle)

```simple
# src/transform/feature/Checkout/entity_view/CheckoutModel.spl

from feature/Checkout/app import CheckoutUseCase  # ❌ CYCLE

fn adapt_for_checkout():
    CheckoutUseCase.do_something()  # Creates circular dependency
```

**Why forbidden:** Transform is a bridge from entity → feature, not feature → entity.

### ❌ Anti-Pattern 3: Bloated transform (kitchen sink)

```simple
# src/transform/feature/Checkout/entity_view/CheckoutModel.spl

# Re-exporting EVERYTHING
reexport entity/Order/**  # ❌ TOO BROAD
reexport entity/Product/**
reexport entity/Customer/**
reexport entity/Inventory/**
reexport entity/Finance/**
reexport entity/Audit/**
```

**Why bad:** Feature becomes coupled to entire domain model.

**Fix:** Only re-export what the feature actually uses.

### ❌ Anti-Pattern 4: Business logic in transform

```simple
# src/transform/feature/Checkout/entity_view/CheckoutModel.spl

fn process_payment(amount: f64) -> Result:  # ❌ WRONG LAYER
    # Complex payment processing logic...
    if amount > 1000:
        apply_fraud_check()
    charge_credit_card()
```

**Why bad:** Transform should only map/adapt, not implement business rules.

**Fix:** Business logic belongs in `feature/*/app/`, not transform.

---

## Summary

**Dimension transforms provide:**
- ✅ Clean separation between feature and entity dimensions
- ✅ Feature-friendly views without direct coupling
- ✅ Explicit, auditable adaptation layer
- ✅ Type safety across dimensions

**Key rules:**
1. Transform sits between feature and entity
2. Feature imports ONLY transform, never entity
3. Transform imports ONLY entity (and shared), never feature
4. Transform can re-export OR adapt (create new types)
5. Keep transforms minimal (only what feature needs)

**When to use which pattern:**
- **Re-export:** Entity type is already feature-friendly
- **Adapter struct:** Need to rename fields or change shape
- **Aggregation struct:** Need to combine multiple entities
- **Projection struct:** Need simplified read-only view

---

## Example 6: HR / Employee — One Entity, Multiple Feature Views

The same `Employee` entity looks very different depending on which feature uses it.

### Entity Dimension

```
src/entity/
  People/
    Employee.spl       # Full employee record (PII, salary, performance, status)
    Department.spl
    Position.spl
    __init__.spl
```

### Feature Dimension

```
src/feature/
  Payroll/             # Needs salary, bank info, tax code
  Onboarding/          # Needs start date, equipment, manager
  DirectoryListing/    # Needs name, title, photo only
```

### Transform Layer

`src/transform/feature/Payroll/__init__.spl`:

```simple
arch {
  dimension = "transform"
  layer = "none"

  transform {
    from = "entity"
    to   = "feature"
    allow_from = ["entity/People/**"]
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

`src/transform/feature/Payroll/entity_view/PayrollModel.spl`:

```simple
from entity/People/Employee import Employee

struct PayrollProfile:
    """
    Payroll-specific view: only salary, tax, and bank details.
    Strips out PII fields not needed by payroll processing.
    """
    employee_id: text
    full_name: text
    salary_cents: i64
    tax_code: text
    bank_account: text
    pay_frequency: text

    static fn from_employee(emp: Employee) -> PayrollProfile:
        PayrollProfile(
            employee_id: emp.id,
            full_name: emp.first_name + " " + emp.last_name,
            salary_cents: emp.salary_cents,
            tax_code: emp.tax_code,
            bank_account: emp.bank_account_number,
            pay_frequency: emp.pay_frequency
        )
```

`src/transform/feature/DirectoryListing/entity_view/DirectoryModel.spl`:

```simple
from entity/People/Employee import Employee
from entity/People/Department import Department

struct DirectoryEntry:
    """
    Public directory view: name, title, photo only — no PII.
    """
    display_name: text
    title: text
    department_name: text
    photo_url: text
    email: text

    static fn from_employee(emp: Employee, dept: Department) -> DirectoryEntry:
        DirectoryEntry(
            display_name: emp.preferred_name,
            title: emp.position.title,
            department_name: dept.name,
            photo_url: emp.photo_url ?? "/avatars/default.png",
            email: emp.work_email
        )
```

**Key insight:** The same `Employee` entity serves three features — each gets only the fields it needs.
The entity never "knows" which features use it.

---

## Example 7: Content Management — One Article, Many Surfaces

An `Article` entity is published to the public site, managed in the CMS, and indexed by search.

### Entity Dimension

```
src/entity/
  Content/
    Article.spl        # Full article (body, metadata, authors, revisions, SEO)
    Author.spl
    Tag.spl
    Revision.spl
    __init__.spl
```

### Feature Dimension

```
src/feature/
  PublicSite/          # Needs rendered HTML, SEO meta, published date only
  CmsEditor/           # Needs full editing surface, revision history
  SearchIndex/         # Needs title, excerpt, tags, author — for search ranking
```

### Transform Layer

`src/transform/feature/PublicSite/__init__.spl`:

```simple
arch {
  dimension = "transform"
  layer = "none"

  transform {
    from = "entity"
    to   = "feature"
    allow_from = ["entity/Content/**"]
  }

  imports {
    allow = ["entity/**", "shared/**"]
    deny  = ["feature/**"]
  }
}
```

`src/transform/feature/PublicSite/entity_view/PublicArticle.spl`:

```simple
from entity/Content/Article import Article
from entity/Content/Author import Author

struct PublicArticle:
    """
    Read-only public view: rendered content + SEO metadata.
    CMS revision history and draft state are excluded.
    """
    slug: text
    title: text
    html_body: text
    excerpt: text
    author_name: text
    author_bio: text
    published_at: text
    tags: [text]
    seo_title: text
    seo_description: text
    canonical_url: text

    static fn from_article(article: Article, author: Author) -> PublicArticle:
        PublicArticle(
            slug: article.slug,
            title: article.title,
            html_body: article.rendered_body,
            excerpt: article.excerpt,
            author_name: author.display_name,
            author_bio: author.short_bio,
            published_at: article.published_at ?? "",
            tags: article.tags.map(\t: t.name),
            seo_title: article.seo_title ?? article.title,
            seo_description: article.seo_description ?? article.excerpt,
            canonical_url: article.canonical_url
        )
```

`src/transform/feature/SearchIndex/entity_view/SearchDocument.spl`:

```simple
from entity/Content/Article import Article

struct SearchDocument:
    """
    Flattened search-indexing view.
    Optimized for ranking signals, not rendering.
    """
    id: text
    title: text
    excerpt: text
    body_text: text   # plain text, no HTML
    author_names: [text]
    tag_names: [text]
    published_at: text
    word_count: i64
    reading_time_minutes: i64

    static fn from_article(article: Article) -> SearchDocument:
        val word_count = article.plain_body.split(" ").len()
        SearchDocument(
            id: article.id,
            title: article.title,
            excerpt: article.excerpt,
            body_text: article.plain_body,
            author_names: article.authors.map(\a: a.display_name),
            tag_names: article.tags.map(\t: t.name),
            published_at: article.published_at ?? "",
            word_count: word_count,
            reading_time_minutes: word_count / 200
        )
```

---

## Example 8: SaaS Multi-Tenant — Organization Across Features

An `Organization` entity contains everything about a tenant, but each feature slice needs a different view.

### Entity Dimension

```
src/entity/
  Tenant/
    Organization.spl    # Full org record (plan, billing, quotas, settings, members)
    Subscription.spl    # Active subscription and billing cycle
    UsageQuota.spl      # Resource usage against limits
    OrgMember.spl       # Members + roles within org
    __init__.spl
```

### Feature Dimension

```
src/feature/
  BillingDashboard/    # Needs invoice history, payment method, plan details
  OrgSettings/         # Needs name, logo, SSO config, notification prefs
  Provisioning/        # Needs quota limits, active features, region config
  MemberManagement/    # Needs member list, roles, invitations
```

### Transform Layer

`src/transform/feature/BillingDashboard/__init__.spl`:

```simple
arch {
  dimension = "transform"
  layer = "none"

  transform {
    from = "entity"
    to   = "feature"
    allow_from = ["entity/Tenant/Organization/**", "entity/Tenant/Subscription/**"]
  }

  imports {
    allow = ["entity/Tenant/**", "shared/**"]
    deny  = ["feature/**"]
  }
}
```

`src/transform/feature/BillingDashboard/entity_view/BillingView.spl`:

```simple
from entity/Tenant/Organization import Organization
from entity/Tenant/Subscription import Subscription

struct BillingView:
    """
    Billing dashboard view: plan, payment method, and renewal info.
    Hides internal provisioning and quota details.
    """
    org_id: text
    org_name: text
    plan_name: text
    plan_price_cents: i64
    billing_cycle: text        # "monthly" | "annual"
    next_renewal_date: text
    payment_method_last4: text
    is_past_due: bool

    static fn from_org_and_sub(
        org: Organization,
        sub: Subscription
    ) -> BillingView:
        BillingView(
            org_id: org.id,
            org_name: org.display_name,
            plan_name: sub.plan.name,
            plan_price_cents: sub.current_price_cents,
            billing_cycle: sub.cycle,
            next_renewal_date: sub.next_renewal_at,
            payment_method_last4: org.payment_method.last4 ?? "N/A",
            is_past_due: sub.status == "past_due"
        )

struct ProvisioningConfig:
    """
    Provisioning view: resource limits and enabled features.
    Only for infrastructure layer use.
    """
    org_id: text
    max_users: i64
    max_storage_gb: i64
    enabled_features: [text]
    deployment_region: text

    static fn from_org(org: Organization) -> ProvisioningConfig:
        ProvisioningConfig(
            org_id: org.id,
            max_users: org.quota.max_users,
            max_storage_gb: org.quota.max_storage_gb,
            enabled_features: org.enabled_feature_flags,
            deployment_region: org.region
        )
```

---

## Example 9: IoT / Monitoring — Device Across Alert and Telemetry Features

A `Device` entity tracks physical hardware, but alert processing and telemetry storage need very different views.

### Entity Dimension

```
src/entity/
  IoT/
    Device.spl          # Full device record (firmware, location, config, owner)
    Telemetry.spl       # Time-series readings (temperature, pressure, etc.)
    AlertRule.spl       # Threshold rules for anomaly detection
    __init__.spl
```

### Feature Dimension

```
src/feature/
  AlertProcessing/     # Needs device identity + alert rules + current readings
  TelemetryStorage/    # Needs device ID + raw reading structs for time-series DB
  DeviceConfig/        # Needs firmware version, config payload, OTA update state
```

### Transform Layer

`src/transform/feature/AlertProcessing/__init__.spl`:

```simple
arch {
  dimension = "transform"
  layer = "none"

  transform {
    from = "entity"
    to   = "feature"
    allow_from = ["entity/IoT/Device/**", "entity/IoT/AlertRule/**", "entity/IoT/Telemetry/**"]
  }

  imports {
    allow = ["entity/IoT/**", "shared/**"]
    deny  = ["feature/**"]
  }
}
```

`src/transform/feature/AlertProcessing/entity_view/AlertContext.spl`:

```simple
from entity/IoT/Device import Device
from entity/IoT/AlertRule import AlertRule
from entity/IoT/Telemetry import Telemetry

struct AlertContext:
    """
    Alert processing view: device identity + active rules + latest readings.
    Optimized for fast threshold evaluation loops.
    """
    device_id: text
    device_name: text
    device_type: text
    location_label: text
    active_rules: [AlertRuleView]
    latest_readings: [ReadingView]

struct AlertRuleView:
    rule_id: text
    metric_name: text
    operator: text     # "gt" | "lt" | "eq"
    threshold: f64
    severity: text     # "info" | "warn" | "critical"

struct ReadingView:
    metric_name: text
    value: f64
    recorded_at: text

fn build_alert_context(device: Device, rules: [AlertRule], readings: [Telemetry]) -> AlertContext:
    val rule_views = rules.map(\r:
        AlertRuleView(
            rule_id: r.id,
            metric_name: r.metric,
            operator: r.operator,
            threshold: r.threshold_value,
            severity: r.severity_level
        )
    )
    val reading_views = readings.map(\t:
        ReadingView(
            metric_name: t.metric_name,
            value: t.value,
            recorded_at: t.timestamp
        )
    )
    AlertContext(
        device_id: device.id,
        device_name: device.display_name,
        device_type: device.device_type,
        location_label: device.location.label,
        active_rules: rule_views,
        latest_readings: reading_views
    )
```

---

## Candidate Selection Guide

When deciding which patterns to use for a new feature's transform:

| Situation | Recommended Transform Pattern |
|-----------|------------------------------|
| Entity already matches feature needs | Re-export (no adaptation needed) |
| Feature uses different terminology | Adapter struct with renamed fields |
| Feature needs fields from 2-3 entities | Aggregation struct with `build(e1, e2)` factory |
| Feature only needs 3-4 of 20 fields | Projection struct (slimmed view) |
| Multiple features use same entity differently | One transform folder per feature |
| Feature needs computed/derived values | Transform struct with static `from_*` method |
| Sensitive fields must be hidden | Explicit struct (never re-export — adapter only) |
| Feature has 1:many relation with entity | Flatten in transform (e.g., orders → line item list) |

### Quick-Start Checklist for a New Transform

```
1. Create transform/feature/<FeatureName>/__init__.spl
   - Set dimension = "transform"
   - Declare transform { from = "entity", to = "feature" }
   - Set allow_from = [only entity modules this feature actually needs]

2. Create transform/feature/<FeatureName>/entity_view/__init__.spl

3. Create transform/feature/<FeatureName>/entity_view/<FeatureName>Model.spl
   - Import entity types
   - Define feature-friendly struct(s)
   - Add static fn from_entity(e: Entity) -> FeatureStruct: factory method

4. Update feature/__init__.spl
   - Add: uses_transform = "transform/feature/<FeatureName>"
   - Add: deny = ["entity/**"]

5. Update feature/<FeatureName>/app/*.spl
   - Replace: from entity/... import ...
   - With:    from transform/feature/<FeatureName>/entity_view import ...
```
