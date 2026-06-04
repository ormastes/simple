# Restaurant Webapp Specification

> 1. Then file contains

<!-- sdn-diagram:id=restaurant_webapp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=restaurant_webapp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

restaurant_webapp_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=restaurant_webapp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Restaurant Webapp Specification

## Scenarios

### Restaurant Webapp Structure

#### has main entry point with WebApp.new

1. Then file contains

2. Then file contains

3. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/main.spl", "WebApp.new")
Then_file_contains("examples/06_io/restaurant_webapp/main.spl", "mount_routes")
Then_file_contains("examples/06_io/restaurant_webapp/main.spl", "app.start")
```

</details>

#### has app.sdn configuration

1. Then file contains

2. Then file contains

3. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/app.sdn", "simple-restaurant")
Then_file_contains("examples/06_io/restaurant_webapp/app.sdn", "database")
Then_file_contains("examples/06_io/restaurant_webapp/app.sdn", "session")
```

</details>

#### has routes.sdn with admin and public routes

1. Then file contains

2. Then file contains

3. Then file contains

4. Then file contains

5. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/routes.sdn", "AdminController")
Then_file_contains("examples/06_io/restaurant_webapp/routes.sdn", "MenuController")
Then_file_contains("examples/06_io/restaurant_webapp/routes.sdn", "OrderController")
Then_file_contains("examples/06_io/restaurant_webapp/routes.sdn", "/admin/login")
Then_file_contains("examples/06_io/restaurant_webapp/routes.sdn", "/menu")
```

</details>

### Restaurant Database Migrations

#### defines admin_users table

1. Then migration has table


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_migration_has_table("examples/06_io/restaurant_webapp/db/migrations.spl", "admin_users")
```

</details>

#### defines templates table with type and default flag

1. Then file contains

2. Then file contains

3. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "templates")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "template_type")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "is_default")
```

</details>

#### defines menu_groups with template foreign key

1. Then file contains

2. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "menu_groups")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "FOREIGN KEY (template_id)")
```

</details>

#### defines menu_items with group foreign key and price

1. Then file contains

2. Then file contains

3. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "menu_items")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "FOREIGN KEY (group_id)")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "price INTEGER")
```

</details>

#### defines menu_conditions for conditional availability

1. Then file contains

2. Then file contains

3. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "menu_conditions")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "condition_type")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "condition_value")
```

</details>

#### defines additional_menus for extras

1. Then file contains

2. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "additional_menus")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "parent_item_id")
```

</details>

#### defines orders table with status and payment

1. Then file contains

2. Then file contains

3. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "orders")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "payment_status")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "items_json")
```

</details>

#### seeds default restaurant and store templates

1. Then file contains

2. Then file contains

3. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "Default Restaurant")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "Default Store")
Then_file_contains("examples/06_io/restaurant_webapp/db/migrations.spl", "Appetizers")
```

</details>

### Restaurant Models DbCodec

#### RestaurantTemplate uses DbCodec with encode/decode

1. Then file contains

2. Then file contains

3. Then file contains

4. Then file contains

5. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/models/template.spl", "class RestaurantTemplate")
Then_file_contains("examples/06_io/restaurant_webapp/models/template.spl", "class RestaurantTemplateCodec")
Then_file_contains("examples/06_io/restaurant_webapp/models/template.spl", "fn encode")
Then_file_contains("examples/06_io/restaurant_webapp/models/template.spl", "fn decode")
Then_file_contains("examples/06_io/restaurant_webapp/models/template.spl", "Repository<RestaurantTemplate>")
```

</details>

#### MenuItem model has price and availability

1. Then file contains

2. Then file contains

3. Then file contains

4. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/models/menu_item.spl", "class MenuItem")
Then_file_contains("examples/06_io/restaurant_webapp/models/menu_item.spl", "price: i64")
Then_file_contains("examples/06_io/restaurant_webapp/models/menu_item.spl", "available: bool")
Then_file_contains("examples/06_io/restaurant_webapp/models/menu_item.spl", "fn format_price")
```

</details>

#### MenuCondition supports time and day conditions

1. Then file contains

2. Then file contains

3. Then file contains

4. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/models/condition.spl", "class MenuCondition")
Then_file_contains("examples/06_io/restaurant_webapp/models/condition.spl", "fn evaluate_condition")
Then_file_contains("examples/06_io/restaurant_webapp/models/condition.spl", "time_after")
Then_file_contains("examples/06_io/restaurant_webapp/models/condition.spl", "day_of_week")
```

</details>

#### Order model tracks status workflow and payment

1. Then file contains

2. Then file contains

3. Then file contains

4. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/models/order.spl", "class Order")
Then_file_contains("examples/06_io/restaurant_webapp/models/order.spl", "status: text")
Then_file_contains("examples/06_io/restaurant_webapp/models/order.spl", "payment_status: text")
Then_file_contains("examples/06_io/restaurant_webapp/models/order.spl", "fn format_order_sticker")
```

</details>

### Restaurant Controllers Web Framework

#### AdminController uses ControllerContext and CSRF

1. Then file contains

2. Then file contains

3. Then file contains

4. Then file contains

5. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "ControllerContext")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "csrf_token_for_session")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "verify_csrf_token")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "render_page")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "render_redirect")
```

</details>

#### AdminController has session-based auth

1. Then file contains

2. Then file contains

3. Then file contains

4. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "session_set")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "session_get")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "session_destroy")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "require_admin")
```

</details>

#### AdminController implements full template CRUD

1. Then file contains

2. Then file contains

3. Then file contains

4. Then file contains

5. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "action_templates_index")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "action_template_create")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "action_template_edit")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "action_template_update")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "action_template_delete")
```

</details>

#### AdminController handles groups, items, conditions, additional menus

1. Then file contains

2. Then file contains

3. Then file contains

4. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "action_group_create")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "action_item_create")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "action_condition_create")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/admin_controller.spl", "action_additional_create")
```

</details>

#### MenuController serves public menu with @public annotation

1. Then file contains

2. Then file contains

3. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/controllers/menu_controller.spl", "@public")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/menu_controller.spl", "action_index")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/menu_controller.spl", "action_show")
```

</details>

#### OrderController has send_to_cook and print_sticker

1. Then file contains

2. Then file contains

3. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/controllers/order_controller.spl", "action_send_to_cook")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/order_controller.spl", "action_print_sticker")
Then_file_contains("examples/06_io/restaurant_webapp/controllers/order_controller.spl", "format_order_sticker")
```

</details>

### Restaurant Views Template SSR

#### layout wraps all pages with nav and flash

1. Then file contains

2. Then file contains

3. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/views/layouts/application.html", "{{content}}")
Then_file_contains("examples/06_io/restaurant_webapp/views/layouts/application.html", "{{>shared/_flash}}")
Then_file_contains("examples/06_io/restaurant_webapp/views/layouts/application.html", "navbar")
```

</details>

#### admin login form has CSRF token

1. Then file contains

2. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/views/admin/login.html", "csrf_token")
Then_file_contains("examples/06_io/restaurant_webapp/views/admin/login.html", "{{#layout")
```

</details>

#### menu show page renders groups and items with conditions

1. Then file contains

2. Then file contains

3. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/views/menu/show.html", "{{#each groups}}")
Then_file_contains("examples/06_io/restaurant_webapp/views/menu/show.html", "{{#each items}}")
Then_file_contains("examples/06_io/restaurant_webapp/views/menu/show.html", "condition-badge")
```

</details>

### Restaurant Webapp Edge Cases

<details>
<summary>Advanced: format_price handles zero cents</summary>

#### format_price handles zero cents

1. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/models/menu_item.spl", "fn format_price")
```

</details>


</details>

<details>
<summary>Advanced: order sticker format includes all key fields</summary>

#### order sticker format includes all key fields

1. Then file contains

2. Then file contains

3. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/models/order.spl", "ORDER #")
Then_file_contains("examples/06_io/restaurant_webapp/models/order.spl", "Table:")
Then_file_contains("examples/06_io/restaurant_webapp/models/order.spl", "Total:")
```

</details>


</details>

<details>
<summary>Advanced: condition evaluator handles unknown types gracefully</summary>

#### condition evaluator handles unknown types gracefully

1. Then file contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Then_file_contains("examples/06_io/restaurant_webapp/models/condition.spl", "true")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/restaurant_webapp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Restaurant Webapp Structure
- Restaurant Database Migrations
- Restaurant Models DbCodec
- Restaurant Controllers Web Framework
- Restaurant Views Template SSR
- Restaurant Webapp Edge Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
