# Dependency Injection Specification

> Integration tests for DI Container with realistic service patterns.

<!-- sdn-diagram:id=di_injection_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=di_injection_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

di_injection_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=di_injection_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dependency Injection Specification

Integration tests for DI Container with realistic service patterns.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DI-INJ-001 to #DI-INJ-007 |
| Category | Runtime \| Dependency Injection |
| Status | Implemented |
| Source | `test/03_system/feature/usage/di_injection_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

**Tags:** di, integration

Integration tests for DI Container with realistic service patterns.
Tests focus on scenarios not covered by unit tests.

## Scenarios

### Service with Dependencies

#### creates service with repository dependency

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Direct construction simulates what a DI container would do
val repo = Repository(name: "users")
val service = UserService(repo: repo)

expect service.repo.name == "users"
```

</details>

#### chains multiple text dependencies

1. var container = TextContainer empty
2. container set
3. container set


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Three-level dependency chain: App -> Service -> Config
var container = TextContainer.empty()

# Level 1: Config
container.set("DbConfig", "db://localhost:5432")

# Level 2: Service depends on Config
val config = container.get("DbConfig")
expect config.?
val pool = "pool:{config.unwrap()}"
container.set("ConnectionPool", pool)

# Level 3: App depends on Service
val pool_value = container.get("ConnectionPool")
expect pool_value.?
val app = "app using {pool_value.unwrap()}"

expect app == "app using pool:db://localhost:5432"
```

</details>

### Profile-Based Configuration

#### profile enum converts to text

1. expect p name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Profile.Test
expect p.name() == "test"
```

</details>

#### profile enum parses from text

1. expect p name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Profile.from_text("prod")
expect p.name() == "prod"
```

</details>

#### profile defaults to dev for unknown

1. expect p name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Profile.from_text("unknown")
expect p.name() == "dev"
```

</details>

#### all profiles have unique names

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test = Profile.Test.name()
val dev = Profile.Dev.name()
val prod = Profile.Prod.name()
val sdn = Profile.Sdn.name()

expect test != dev
expect dev != prod
expect prod != sdn
```

</details>

### Container Binding Pattern

#### stores and retrieves values

1. var container = TextContainer empty
2. container set
3. expect result unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var container = TextContainer.empty()
container.set("service", "my_service")

val result = container.get("service")
expect result.?
expect result.unwrap() == "my_service"
```

</details>

#### has returns true for existing keys

1. var container = TextContainer empty
2. container set
3. expect container has
4. expect not container has


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var container = TextContainer.empty()
container.set("key", "value")

expect container.has("key")
expect not container.has("missing")
```

</details>

#### get returns None for missing keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val container = TextContainer.empty()
val result = container.get("missing")

expect not result.?
```

</details>

#### set overwrites existing values

1. var container = TextContainer empty
2. container set
3. container set
4. expect result unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var container = TextContainer.empty()
container.set("key", "first")
container.set("key", "second")

val result = container.get("key")
expect result.?
expect result.unwrap() == "second"
```

</details>

### DI Error Handling Pattern

#### returns Ok for existing binding

1. expect result unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: Dict<text, text> = {"Service": "instance"}
val result = resolve(data, "Service")

expect result.ok.?
expect result.unwrap() == "instance"
```

</details>

#### returns Err for missing binding

1. expect err msg starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: Dict<text, text> = {}
val result = resolve(data, "Missing")

expect result.err.?
val err_msg = result.unwrap_err()
expect err_msg.starts_with("No binding")
```

</details>

### @inject Decorator Recognition

#### function with @inject is parsed

1. fn create service
2. expect create service


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@inject
fn create_service(config: text) -> text:
    "service:{config}"

# The function exists and is callable
# (decorator doesn't break parsing)
expect create_service("test") == "service:test"
```

</details>

#### class method with @inject is parsed

1. static fn create
2. Database


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Database:
    connection: text

    @inject
    static fn create(connection: text) -> Database:
        Database(connection: connection)

val db = Database.create("db://localhost")
expect db.connection == "db://localhost"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
