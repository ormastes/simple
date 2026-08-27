# Dependency Injection Specification

> Integration tests for DI Container with realistic service patterns.

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
| Source | `test/feature/usage/di_injection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**Tags:** di, integration

Integration tests for DI Container with realistic service patterns.
Tests focus on scenarios not covered by unit tests.

## Scenarios

### Service with Dependencies

#### creates service with repository dependency

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates service with repository dependency


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates service with repository dependency")
# Direct construction simulates what a DI container would do
val repo = Repository(name: "users")
val service = UserService(repo: repo)

expect service.repo.name == "users"
```

</details>

#### chains multiple text dependencies

- chains multiple text dependencies


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains multiple text dependencies")
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

- profile enum converts to text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("profile enum converts to text")
val p = Profile.Test
expect p.name() == "test"
```

</details>

#### profile enum parses from text

- profile enum parses from text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("profile enum parses from text")
val p = Profile.from_text("prod")
expect p.name() == "prod"
```

</details>

#### profile defaults to dev for unknown

- profile defaults to dev for unknown


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("profile defaults to dev for unknown")
val p = Profile.from_text("unknown")
expect p.name() == "dev"
```

</details>

#### all profiles have unique names

- all profiles have unique names


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("all profiles have unique names")
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

- stores and retrieves values


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("stores and retrieves values")
var container = TextContainer.empty()
container.set("service", "my_service")

val result = container.get("service")
expect result.?
expect result.unwrap() == "my_service"
```

</details>

#### has returns true for existing keys

- has returns true for existing keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("has returns true for existing keys")
var container = TextContainer.empty()
container.set("key", "value")

expect container.has("key")
expect not container.has("missing")
```

</details>

#### get returns None for missing keys

- get returns None for missing keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("get returns None for missing keys")
val container = TextContainer.empty()
val result = container.get("missing")

expect not result.?
```

</details>

#### set overwrites existing values

- set overwrites existing values


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("set overwrites existing values")
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

- returns Ok for existing binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns Ok for existing binding")
val data: Dict<text, text> = {"Service": "instance"}
val result = resolve(data, "Service")

expect result.ok.?
expect result.unwrap() == "instance"
```

</details>

#### returns Err for missing binding

- returns Err for missing binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns Err for missing binding")
val data: Dict<text, text> = {}
val result = resolve(data, "Missing")

expect result.err.?
val err_msg = result.unwrap_err()
expect err_msg.starts_with("No binding")
```

</details>

### @inject Decorator Recognition

#### function with @inject is parsed

- function with @inject is parsed


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("function with @inject is parsed")
@inject
fn create_service(config: text) -> text:
    "service:{config}"

# The function exists and is callable
# (decorator doesn't break parsing)
expect create_service("test") == "service:test"
```

</details>

#### class method with @inject is parsed

- class method with @inject is parsed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("class method with @inject is parsed")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2ab2c7e1658d1e9d4b91e15827363a0689ed677d3b0492c2fb265d9ef5fdb59c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2ab2c7e1658d1e9d4b91e15827363a0689ed677d3b0492c2fb265d9ef5fdb59c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2ab2c7e1658d1e9d4b91e15827363a0689ed677d3b0492c2fb265d9ef5fdb59c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/di_injection_spec.spl
mirror: doc/06_spec/feature/usage/di_injection_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/di_injection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/di_injection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/di_injection_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates service with repository dependency' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/di_injection_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chains multiple text dependencies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/di_injection_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'profile enum converts to text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
