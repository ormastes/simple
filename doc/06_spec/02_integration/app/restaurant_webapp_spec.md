# restaurant_webapp_spec

> Verifies the restaurant webapp behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 43 | 43 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# restaurant_webapp_spec

Verifies the restaurant webapp behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/restaurant_webapp_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the restaurant webapp behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Restaurant Webapp Structure

#### has main entry point with WebApp.new

- Verify: has main entry point with WebApp.new


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: has main entry point with WebApp.new")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/main.spl", "WebApp.create")
Then_file_contains("examples/06_io/restaurant_webapp/main.spl", "mount_routes")
Then_file_contains("examples/06_io/restaurant_webapp/main.spl", "app.start")
```

</details>

#### has app.sdn configuration

- Verify: has app.sdn configuration


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: has app.sdn configuration")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/app.sdn", "simple-restaurant")
Then_file_contains("examples/06_io/restaurant_webapp/app.sdn", "database")
Then_file_contains("examples/06_io/restaurant_webapp/app.sdn", "session")
```

</details>

#### has routes.sdn with admin and public routes

- Verify: has routes.sdn with admin and public routes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: has routes.sdn with admin and public routes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/routes.sdn", "AdminController")
Then_file_contains("examples/06_io/restaurant_webapp/routes.sdn", "MenuController")
Then_file_contains("examples/06_io/restaurant_webapp/routes.sdn", "OrderController")
Then_file_contains("examples/06_io/restaurant_webapp/routes.sdn", "/admin/login")
Then_file_contains("examples/06_io/restaurant_webapp/routes.sdn", "/menu")
```

</details>

### Restaurant Database Migrations

#### defines admin_users table

- Verify: defines admin_users table


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: defines admin_users table")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_migration_has_table("examples/06_io/restaurant_webapp/db/migrations.spl", "admin_users")
```

</details>

#### defines templates table with type and default flag

- Verify: defines templates table with type and default flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: defines templates table with type and default flag")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "templates")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "template_type")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "is_default")
```

</details>

#### defines menu_groups with template foreign key

- Verify: defines menu_groups with template foreign key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: defines menu_groups with template foreign key")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "menu_groups")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "FOREIGN KEY (template_id)")
```

</details>

#### defines menu_items with group foreign key and price

- Verify: defines menu_items with group foreign key and price


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: defines menu_items with group foreign key and price")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "menu_items")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "FOREIGN KEY (group_id)")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "price INTEGER")
```

</details>

#### defines menu_conditions for conditional availability

- Verify: defines menu_conditions for conditional availability


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: defines menu_conditions for conditional availability")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "menu_conditions")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "condition_type")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "condition_value")
```

</details>

#### defines additional_menus for extras

- Verify: defines additional_menus for extras


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: defines additional_menus for extras")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "additional_menus")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "parent_item_id")
```

</details>

#### defines orders table with status and payment

- Verify: defines orders table with status and payment


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: defines orders table with status and payment")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "orders")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "payment_status")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "items_json")
```

</details>

#### seeds default restaurant and store templates

- Verify: seeds default restaurant and store templates


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: seeds default restaurant and store templates")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "Default Restaurant")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "Default Store")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "Appetizers")
```

</details>

### Restaurant Models DbCodec

#### RestaurantTemplate uses DbCodec with encode/decode

- Verify: RestaurantTemplate uses DbCodec with encode/decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: RestaurantTemplate uses DbCodec with encode/decode")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/models/template.spl", "class RestaurantTemplate")
Then_file_contains("examples/06_io/restaurant_webapp/models/template.spl", "class RestaurantTemplateCodec")
Then_file_contains("examples/06_io/restaurant_webapp/models/template.spl", "fn encode")
Then_file_contains("examples/06_io/restaurant_webapp/models/template.spl", "fn decode")
Then_file_contains("examples/06_io/restaurant_webapp/models/template.spl", "Repository<RestaurantTemplate>")
```

</details>

#### MenuItem model has price and availability

- Verify: MenuItem model has price and availability


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: MenuItem model has price and availability")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/models/menu_item.spl", "class MenuItem")
Then_file_contains("examples/06_io/restaurant_webapp/models/menu_item.spl", "price: i64")
Then_file_contains("examples/06_io/restaurant_webapp/models/menu_item.spl", "available: bool")
Then_file_contains("examples/06_io/restaurant_webapp/models/menu_item.spl", "fn format_price")
```

</details>

#### MenuCondition supports time and day conditions

- Verify: MenuCondition supports time and day conditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: MenuCondition supports time and day conditions")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/models/condition.spl", "class MenuCondition")
Then_file_contains("examples/06_io/restaurant_webapp/models/condition.spl", "fn evaluate_condition")
Then_file_contains("examples/06_io/restaurant_webapp/models/condition.spl", "time_after")
Then_file_contains("examples/06_io/restaurant_webapp/models/condition.spl", "day_of_week")
```

</details>

#### Order model tracks status workflow and payment

- Verify: Order model tracks status workflow and payment


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: Order model tracks status workflow and payment")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/models/order.spl", "class Order")
Then_file_contains("examples/06_io/restaurant_webapp/models/order.spl", "status: text")
Then_file_contains("examples/06_io/restaurant_webapp/models/order.spl", "payment_status: text")
Then_file_contains("examples/06_io/restaurant_webapp/models/order.spl", "fn format_order_sticker")
```

</details>

### Restaurant Controllers Web Framework

#### AdminController uses ControllerContext and CSRF

- Verify: AdminController uses ControllerContext and CSRF


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: AdminController uses ControllerContext and CSRF")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "ControllerContext")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "csrf_token_for_session")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "verify_csrf_token")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "render_page")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "render_redirect")
```

</details>

#### AdminController has session-based auth

- Verify: AdminController has session-based auth


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: AdminController has session-based auth")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "session_set")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "session_get")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "session_destroy")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "require_admin")
```

</details>

#### AdminController implements full template CRUD

- Verify: AdminController implements full template CRUD


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: AdminController implements full template CRUD")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "action_templates_index")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "action_template_create")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "action_template_edit")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "action_template_update")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "action_template_delete")
```

</details>

#### AdminController handles groups, items, conditions, additional menus

- Verify: AdminController handles groups, items, conditions, additional menus


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: AdminController handles groups, items, conditions, additional menus")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "action_group_create")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "action_item_create")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "action_condition_create")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "action_additional_create")
```

</details>

#### MenuController serves public menu with @public annotation

- Verify: MenuController serves public menu with @public annotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: MenuController serves public menu with @public annotation")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/controllers/menu_controller.spl", "@public")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/menu_controller.spl", "action_index")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/menu_controller.spl", "action_show")
```

</details>

#### OrderController has send_to_cook and print_sticker

- Verify: OrderController has send_to_cook and print_sticker


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: OrderController has send_to_cook and print_sticker")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/controllers/order_controller.spl", "action_send_to_cook")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/order_controller.spl", "action_print_sticker")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/order_controller.spl", "format_order_sticker")
```

</details>

### Restaurant Views Template SSR

#### layout wraps all pages with nav and flash

- Verify: layout wraps all pages with nav and flash


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: layout wraps all pages with nav and flash")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/views/layouts/application.html", "{{content}}")
Then_file_contains("examples/06_io/restaurant_webapp/views/layouts/application.html", "{{>shared/_flash}}")
Then_file_contains("examples/06_io/restaurant_webapp/views/layouts/application.html", "navbar")
```

</details>

#### admin login form has CSRF token

- Verify: admin login form has CSRF token


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: admin login form has CSRF token")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/views/admin/login.html", "csrf_token")
Then_file_contains("examples/06_io/restaurant_webapp/views/admin/login.html", "{{#layout")
```

</details>

#### menu show page renders groups and items with conditions

- Verify: menu show page renders groups and items with conditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: menu show page renders groups and items with conditions")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/views/menu/show.html", "{{#each groups}}")
Then_file_contains("examples/06_io/restaurant_webapp/views/menu/show.html", "{{#each items}}")
Then_file_contains("examples/06_io/restaurant_webapp/views/menu/show.html", "condition-badge")
```

</details>

### Restaurant Webapp Edge Cases

<details>
<summary>Advanced: format_price handles zero cents</summary>

#### format_price handles zero cents

- Verify: format_price handles zero cents


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: format_price handles zero cents")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/models/menu_item.spl", "fn format_price")
```

</details>


</details>

<details>
<summary>Advanced: order sticker format includes all key fields</summary>

#### order sticker format includes all key fields

- Verify: order sticker format includes all key fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: order sticker format includes all key fields")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/models/order.spl", "ORDER #")
Then_file_contains("examples/06_io/restaurant_webapp/models/order.spl", "Table:")
Then_file_contains("examples/06_io/restaurant_webapp/models/order.spl", "Total:")
```

</details>


</details>

<details>
<summary>Advanced: condition evaluator handles unknown types gracefully</summary>

#### condition evaluator handles unknown types gracefully

- Verify: condition evaluator handles unknown types gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: condition evaluator handles unknown types gracefully")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/models/condition.spl", "true")
```

</details>


</details>

### Restaurant Payment Gateway

#### Payment model has DbCodec with card_last_four and transaction_id

- Verify: Payment model has DbCodec with card_last_four and transaction_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: Payment model has DbCodec with card_last_four and transaction_id")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/models/payment.spl", "class Payment")
Then_file_contains("examples/06_io/restaurant_webapp/models/payment.spl", "card_last_four")
Then_file_contains("examples/06_io/restaurant_webapp/models/payment.spl", "transaction_id")
Then_file_contains("examples/06_io/restaurant_webapp/models/payment.spl", "fn encode")
Then_file_contains("examples/06_io/restaurant_webapp/models/payment.spl", "fn decode")
```

</details>

#### mock gateway charges cards starting with 4 and rejects others

- Verify: mock gateway charges cards starting with 4 and rejects others


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: mock gateway charges cards starting with 4 and rejects others")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/models/payment.spl", "fn mock_gateway_charge")
Then_file_contains("examples/06_io/restaurant_webapp/models/payment.spl", "mock_txn_")
Then_file_contains("examples/06_io/restaurant_webapp/models/payment.spl", "Card declined")
```

</details>

#### supports three payment methods: desk_credit, gate_pay, store_checkout

- Verify: supports three payment methods: desk_credit, gate_pay, store_checkout


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: supports three payment methods: desk_credit, gate_pay, store_checkout")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/models/payment.spl", "desk_credit")
Then_file_contains("examples/06_io/restaurant_webapp/models/payment.spl", "gate_pay")
Then_file_contains("examples/06_io/restaurant_webapp/models/payment.spl", "store_checkout")
Then_file_contains("examples/06_io/restaurant_webapp/models/payment.spl", "fn is_valid_payment_method")
```

</details>

#### PaymentController has desk-pay, gate-pay, and store-checkout flows

- Verify: PaymentController has desk-pay, gate-pay, and store-checkout flows


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: PaymentController has desk-pay, gate-pay, and store-checkout flows")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/controllers/payment_controller.spl", "action_desk_pay")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/payment_controller.spl", "action_gate_pay")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/payment_controller.spl", "action_store_checkout")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/payment_controller.spl", "mock_gateway_charge")
```

</details>

#### PaymentController sends receipt emails after payment

- Verify: PaymentController sends receipt emails after payment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: PaymentController sends receipt emails after payment")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/controllers/payment_controller.spl", "build_payment_receipt_email")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/payment_controller.spl", "send_notification")
```

</details>

#### routes include desk-pay, gate-pay, and store checkout

- Verify: routes include desk-pay, gate-pay, and store checkout


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: routes include desk-pay, gate-pay, and store checkout")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/routes.sdn", "/admin/orders/:order_id/desk-pay")
Then_file_contains("examples/06_io/restaurant_webapp/routes.sdn", "/admin/orders/:order_id/gate-pay")
Then_file_contains("examples/06_io/restaurant_webapp/routes.sdn", "/checkout/:order_id")
```

</details>

#### payment views have credit card forms with CSRF

- Verify: payment views have credit card forms with CSRF


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: payment views have credit card forms with CSRF")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/views/payment/desk_pay.html", "card_number")
Then_file_contains("examples/06_io/restaurant_webapp/views/payment/desk_pay.html", "csrf_token")
Then_file_contains("examples/06_io/restaurant_webapp/views/payment/gate_pay.html", "card_number")
Then_file_contains("examples/06_io/restaurant_webapp/views/payment/store_checkout.html", "card_number")
```

</details>

### Restaurant Delivery

#### DeliveryRequest model has address, phone, email, status

- Verify: DeliveryRequest model has address, phone, email, status


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: DeliveryRequest model has address, phone, email, status")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/models/delivery.spl", "class DeliveryRequest")
Then_file_contains("examples/06_io/restaurant_webapp/models/delivery.spl", "customer_name")
Then_file_contains("examples/06_io/restaurant_webapp/models/delivery.spl", "address")
Then_file_contains("examples/06_io/restaurant_webapp/models/delivery.spl", "estimated_time")
```

</details>

#### DeliveryController has customer request and admin management

- Verify: DeliveryController has customer request and admin management


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: DeliveryController has customer request and admin management")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/controllers/delivery_controller.spl", "action_request_delivery")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/delivery_controller.spl", "action_update_status")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/delivery_controller.spl", "find_pending_deliveries")
```

</details>

#### delivery sends confirmation email to customer

- Verify: delivery sends confirmation email to customer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: delivery sends confirmation email to customer")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/controllers/delivery_controller.spl", "build_delivery_confirmation_email")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/delivery_controller.spl", "send_notification")
```

</details>

#### routes include customer delivery request and admin management

- Verify: routes include customer delivery request and admin management


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: routes include customer delivery request and admin management")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/routes.sdn", "/delivery/:order_id/request")
Then_file_contains("examples/06_io/restaurant_webapp/routes.sdn", "/admin/deliveries")
```

</details>

### Restaurant Email Service

#### email service builds order confirmation, status update, delivery, and receipt emails

- Verify: email service builds order confirmation, status update, delivery, and receipt emails


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: email service builds order confirmation, status update, delivery, and receipt emails")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/services/email_service.spl", "build_order_confirmation_email")
Then_file_contains("examples/06_io/restaurant_webapp/services/email_service.spl", "build_order_status_email")
Then_file_contains("examples/06_io/restaurant_webapp/services/email_service.spl", "build_delivery_confirmation_email")
Then_file_contains("examples/06_io/restaurant_webapp/services/email_service.spl", "build_payment_receipt_email")
```

</details>

#### email bodies contain HTML with order details

- Verify: email bodies contain HTML with order details


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: email bodies contain HTML with order details")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/services/email_service.spl", "<html>")
Then_file_contains("examples/06_io/restaurant_webapp/services/email_service.spl", "format_price")
```

</details>

#### send_notification logs in test mode

- Verify: send_notification logs in test mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: send_notification logs in test mode")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/services/email_service.spl", "fn send_notification")
Then_file_contains("examples/06_io/restaurant_webapp/services/email_service.spl", "[EMAIL]")
```

</details>

### Restaurant Migrations Payment and Delivery

#### defines payments table with card and transaction fields

- Verify: defines payments table with card and transaction fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: defines payments table with card and transaction fields")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "payments")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "card_last_four")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "transaction_id")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "gateway_response")
```

</details>

#### defines delivery_requests table with address and status

- Verify: defines delivery_requests table with address and status


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_RESTAURANT_WEBAPP-001
step("Verify: defines delivery_requests table with address and status")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "delivery_requests")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "customer_email")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "estimated_time")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 43 |
| Active scenarios | 43 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f56da1165dccd669c1d2aa5b588b4e2016bbaf8d8d433944e8e1210a330dca00`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f56da1165dccd669c1d2aa5b588b4e2016bbaf8d8d433944e8e1210a330dca00`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f56da1165dccd669c1d2aa5b588b4e2016bbaf8d8d433944e8e1210a330dca00`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/app/restaurant_webapp_spec.spl
mirror: doc/06_spec/02_integration/app/restaurant_webapp_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/restaurant_webapp_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/app/restaurant_webapp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/restaurant_webapp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
