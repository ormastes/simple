# Layer Checker Specification

> <details>

<!-- sdn-diagram:id=layer_checker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=layer_checker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

layer_checker_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=layer_checker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 43 | 43 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layer Checker Specification

## Scenarios

### check_layer_dep

#### allows upper to depend on lower (UpperToLower)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(
    ["api", "app", "domain", "infra"],
    LayerDirection.UpperToLower
)
# api (0) -> domain (2): upper depends on lower = allowed
val result = check_layer_dep(layer, "api", "domain")
expect(result).to_equal(true)
```

</details>

#### denies lower to depend on upper (UpperToLower)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(
    ["api", "app", "domain", "infra"],
    LayerDirection.UpperToLower
)
# infra (3) -> api (0): lower depends on upper = denied
val result = check_layer_dep(layer, "infra", "api")
expect(result).to_equal(false)
```

</details>

#### allows same layer dependency by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(
    ["api", "app", "domain"],
    LayerDirection.UpperToLower
)
val result = check_layer_dep(layer, "app", "app")
expect(result).to_equal(true)
```

</details>

#### allows unknown layers through

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(
    ["api", "app"],
    LayerDirection.UpperToLower
)
# unknown layer -> known layer: unrestricted
val result = check_layer_dep(layer, "external", "api")
expect(result).to_equal(true)
```

</details>

#### both unknown layers allowed

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(
    ["api", "app"],
    LayerDirection.UpperToLower
)
val result = check_layer_dep(layer, "unknown1", "unknown2")
expect(result).to_equal(true)
```

</details>

#### allows lower to depend on upper (LowerToUpper)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(
    ["api", "app", "domain", "infra"],
    LayerDirection.LowerToUpper
)
# infra (3) -> api (0): lower depends on upper = allowed
val result = check_layer_dep(layer, "infra", "api")
expect(result).to_equal(true)
```

</details>

#### denies upper to depend on lower (LowerToUpper)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(
    ["api", "app", "domain", "infra"],
    LayerDirection.LowerToUpper
)
# api (0) -> infra (3): upper depends on lower = denied
val result = check_layer_dep(layer, "api", "infra")
expect(result).to_equal(false)
```

</details>

#### empty layer def allows everything

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.empty()
val result = check_layer_dep(layer, "anything", "else")
expect(result).to_equal(true)
```

</details>

### LayerChecker construction

#### creates checker with layer def

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(
    ["api", "app", "domain", "infra"],
    LayerDirection.UpperToLower
)
val checker = LayerChecker.new(layer)
expect(checker.layer_def.order.len()).to_equal(4)
```

</details>

#### creates checker with empty layers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.empty()
val checker = LayerChecker.new(layer)
expect(checker.layer_def.order.len()).to_equal(0)
```

</details>

### LayerChecker assign_module_layer

#### registers module with a layer

1. var checker = LayerChecker new
2. checker assign module layer
   - Expected: assigned equals `domain`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("src/auth/login.spl", "domain")
val assigned = checker.get_module_layer("src/auth/login.spl") ?? ""
expect(assigned).to_equal("domain")
```

</details>

#### registers multiple modules

1. var checker = LayerChecker new
2. checker assign module layer
3. checker assign module layer
4. checker assign module layer
   - Expected: l1 equals `api`
   - Expected: l2 equals `app`
   - Expected: l3 equals `domain`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("auth/handler.spl", "api")
checker.assign_module_layer("auth/service.spl", "app")
checker.assign_module_layer("auth/repo.spl", "domain")
val l1 = checker.get_module_layer("auth/handler.spl") ?? ""
val l2 = checker.get_module_layer("auth/service.spl") ?? ""
val l3 = checker.get_module_layer("auth/repo.spl") ?? ""
expect(l1).to_equal("api")
expect(l2).to_equal("app")
expect(l3).to_equal("domain")
```

</details>

#### returns empty string for unregistered module

1. var checker = LayerChecker new
   - Expected: assigned equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
val assigned = checker.get_module_layer("unknown.spl") ?? ""
expect(assigned).to_equal("")
```

</details>

### LayerChecker check_dependency

#### allows valid upper-to-lower dependency

1. var checker = LayerChecker new
2. checker assign module layer
3. checker assign module layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("handler.spl", "api")
checker.assign_module_layer("service.spl", "app")
val violation = checker.check_dependency("handler.spl", "service.spl")
expect(violation).to_be_nil()
```

</details>

#### detects invalid lower-to-upper dependency

1. var checker = LayerChecker new
2. checker assign module layer
3. checker assign module layer
   - Expected: is_denied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("repo.spl", "infra")
checker.assign_module_layer("handler.spl", "api")
val violation = checker.check_dependency("repo.spl", "handler.spl")
val is_denied = violation.?
expect(is_denied).to_equal(true)
```

</details>

#### allows dependency between unregistered modules

1. var checker = LayerChecker new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
# neither module is registered - no restriction
val violation = checker.check_dependency("unknown1.spl", "unknown2.spl")
expect(violation).to_be_nil()
```

</details>

#### allows dependency when source is unregistered

1. var checker = LayerChecker new
2. checker assign module layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("app.spl", "app")
# unregistered -> app: no restriction
val violation = checker.check_dependency("unknown.spl", "app.spl")
expect(violation).to_be_nil()
```

</details>

#### allows same-layer dependency

1. var checker = LayerChecker new
2. checker assign module layer
3. checker assign module layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("service_a.spl", "app")
checker.assign_module_layer("service_b.spl", "app")
val violation = checker.check_dependency("service_a.spl", "service_b.spl")
expect(violation).to_be_nil()
```

</details>

#### skips layers when allowed

1. var checker = LayerChecker new
2. checker assign module layer
3. checker assign module layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("handler.spl", "api")
checker.assign_module_layer("repo.spl", "infra")
# api (0) -> infra (3): skip allowed in non-adjacent mode
val violation = checker.check_dependency("handler.spl", "repo.spl")
expect(violation).to_be_nil()
```

</details>

### LayerChecker detect_layer_cycles

#### no cycles in empty checker

1. var checker = LayerChecker new
   - Expected: cycles.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
val cycles = checker.detect_layer_cycles()
expect(cycles.len()).to_equal(0)
```

</details>

#### no cycles in valid dependency chain

1. var checker = LayerChecker new
2. checker assign module layer
3. checker assign module layer
4. checker assign module layer
5. checker add dependency
6. checker add dependency
   - Expected: cycles.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("handler.spl", "api")
checker.assign_module_layer("service.spl", "app")
checker.assign_module_layer("repo.spl", "domain")
checker.add_dependency("handler.spl", "service.spl")
checker.add_dependency("service.spl", "repo.spl")
val cycles = checker.detect_layer_cycles()
expect(cycles.len()).to_equal(0)
```

</details>

#### detects simple two-module cycle

1. var checker = LayerChecker new
2. checker assign module layer
3. checker assign module layer
4. checker add dependency
5. checker add dependency


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("a.spl", "api")
checker.assign_module_layer("b.spl", "app")
checker.add_dependency("a.spl", "b.spl")
checker.add_dependency("b.spl", "a.spl")
val cycles = checker.detect_layer_cycles()
expect(cycles.len()).to_be_greater_than(0)
```

</details>

#### detects three-module cycle

1. var checker = LayerChecker new
2. checker assign module layer
3. checker assign module layer
4. checker assign module layer
5. checker add dependency
6. checker add dependency
7. checker add dependency


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("a.spl", "api")
checker.assign_module_layer("b.spl", "app")
checker.assign_module_layer("c.spl", "domain")
checker.add_dependency("a.spl", "b.spl")
checker.add_dependency("b.spl", "c.spl")
checker.add_dependency("c.spl", "a.spl")
val cycles = checker.detect_layer_cycles()
expect(cycles.len()).to_be_greater_than(0)
```

</details>

#### detects self-cycle

1. var checker = LayerChecker new
2. checker assign module layer
3. checker add dependency


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("a.spl", "api")
checker.add_dependency("a.spl", "a.spl")
val cycles = checker.detect_layer_cycles()
expect(cycles.len()).to_be_greater_than(0)
```

</details>

### LayerChecker bypass grants

#### registers a bypass grant

1. var checker = LayerChecker new
2. checker register bypass grant
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
val grant = BypassGrant.new(
    "infra/db",
    "raw_query",
    "domain->infra",
    "performance critical",
    "infra/db.spl:10"
)
checker.register_bypass_grant(grant)
val found = checker.has_bypass_grant("infra/db", "raw_query")
expect(found).to_equal(true)
```

</details>

#### bypass grant not found for wrong symbol

1. var checker = LayerChecker new
2. checker register bypass grant
   - Expected: found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
val grant = BypassGrant.new("mod", "sym_a", "e", "r", "l")
checker.register_bypass_grant(grant)
val found = checker.has_bypass_grant("mod", "sym_b")
expect(found).to_equal(false)
```

</details>

#### bypass grant not found for wrong module

1. var checker = LayerChecker new
2. checker register bypass grant
   - Expected: found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
val grant = BypassGrant.new("mod_a", "sym", "e", "r", "l")
checker.register_bypass_grant(grant)
val found = checker.has_bypass_grant("mod_b", "sym")
expect(found).to_equal(false)
```

</details>

#### validates matching bypass usage

1. var checker = LayerChecker new
2. checker register bypass grant
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
val grant = BypassGrant.new(
    "infra/db",
    "raw_query",
    "domain->infra",
    "perf",
    "db.spl:10"
)
checker.register_bypass_grant(grant)

val usage = BypassUsage.new(
    "domain/repo",
    "raw_query",
    "domain->infra",
    "need direct db access",
    "repo.spl:20",
    "db.spl:10"
)
val valid = checker.validate_bypass_usage(usage)
expect(valid).to_equal(true)
```

</details>

#### rejects bypass usage without matching grant

1. var checker = LayerChecker new
   - Expected: valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
# No grant registered
val usage = BypassUsage.new(
    "domain/repo",
    "secret_fn",
    "domain->infra",
    "reason",
    "repo.spl:5",
    "other.spl:1"
)
val valid = checker.validate_bypass_usage(usage)
expect(valid).to_equal(false)
```

</details>

### LayerChecker bypass non-transitive

#### bypass cannot be re-exported through chain

1. var checker = LayerChecker new
2. checker register bypass grant
   - Expected: checker.validate_bypass_usage(direct_usage) is true
   - Expected: transitive_valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)

# Grant from infra to domain
val grant = BypassGrant.new(
    "infra/db",
    "raw_query",
    "domain->infra",
    "perf",
    "db.spl:10"
)
checker.register_bypass_grant(grant)

# Usage from domain (valid - direct, edge matches grant)
val direct_usage = BypassUsage.new(
    "domain/repo",
    "raw_query",
    "domain->infra",
    "direct use",
    "repo.spl:20",
    "db.spl:10"
)
expect(checker.validate_bypass_usage(direct_usage)).to_equal(true)

# Usage from api (invalid - transitive, edge does not match grant)
val transitive_usage = BypassUsage.new(
    "api/handler",
    "raw_query",
    "api->infra",
    "transitive attempt",
    "handler.spl:5",
    "db.spl:10"
)
val transitive_valid = checker.validate_bypass_usage(transitive_usage)
expect(transitive_valid).to_equal(false)
```

</details>

#### bypass grant only covers its specified edge

1. var checker = LayerChecker new
2. checker register bypass grant
   - Expected: checker.validate_bypass_usage(matching) is true
   - Expected: checker.validate_bypass_usage(mismatch) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
val grant = BypassGrant.new(
    "infra/db",
    "raw_query",
    "domain->infra",
    "perf",
    "db.spl:10"
)
checker.register_bypass_grant(grant)

# Matching edge: allowed
val matching = BypassUsage.new("domain/x", "raw_query", "domain->infra", "r", "x.spl:1", "db.spl:10")
expect(checker.validate_bypass_usage(matching)).to_equal(true)

# Different edge: denied
val mismatch = BypassUsage.new("app/x", "raw_query", "app->infra", "r", "x.spl:1", "db.spl:10")
expect(checker.validate_bypass_usage(mismatch)).to_equal(false)
```

</details>

### LayerChecker generate_bypass_report

#### empty report with no grants

1. var checker = LayerChecker new
   - Expected: report.grant_count equals `0`
   - Expected: report.usage_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
val report = checker.generate_bypass_report()
expect(report.grant_count).to_equal(0)
expect(report.usage_count).to_equal(0)
```

</details>

#### report counts grants

1. var checker = LayerChecker new
2. checker register bypass grant
3. checker register bypass grant
   - Expected: report.grant_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
checker.register_bypass_grant(BypassGrant.new("m1", "s1", "e1", "r1", "l1"))
checker.register_bypass_grant(BypassGrant.new("m2", "s2", "e2", "r2", "l2"))
val report = checker.generate_bypass_report()
expect(report.grant_count).to_equal(2)
```

</details>

#### report includes grant details

1. var checker = LayerChecker new
2. checker register bypass grant


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain"], LayerDirection.UpperToLower)
var checker = LayerChecker.new(layer)
val grant = BypassGrant.new("infra/db", "raw_query", "domain->infra", "perf", "db.spl:10")
checker.register_bypass_grant(grant)
val report = checker.generate_bypass_report()
val text_report = report.to_text()
expect(text_report).to_contain("raw_query")
expect(text_report).to_contain("infra/db")
```

</details>

### LayerChecker with LowerToUpper direction

#### allows lower module to depend on upper

1. var checker = LayerChecker new
2. checker assign module layer
3. checker assign module layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.LowerToUpper)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("infra_mod.spl", "infra")
checker.assign_module_layer("api_mod.spl", "api")
# infra (3) -> api (0): lower depends on upper = allowed
val violation = checker.check_dependency("infra_mod.spl", "api_mod.spl")
expect(violation).to_be_nil()
```

</details>

#### denies upper module depending on lower

1. var checker = LayerChecker new
2. checker assign module layer
3. checker assign module layer
   - Expected: is_denied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.LowerToUpper)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("api_mod.spl", "api")
checker.assign_module_layer("infra_mod.spl", "infra")
# api (0) -> infra (3): upper depends on lower = denied
val violation = checker.check_dependency("api_mod.spl", "infra_mod.spl")
val is_denied = violation.?
expect(is_denied).to_equal(true)
```

</details>

#### Clean Architecture inward dependency allowed

1. var checker = LayerChecker new
2. checker assign module layer
3. checker assign module layer
4. checker assign module layer
5. checker assign module layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(
    ["entities", "use_cases", "adapters", "frameworks"],
    LayerDirection.LowerToUpper
)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("framework.spl", "frameworks")
checker.assign_module_layer("adapter.spl", "adapters")
checker.assign_module_layer("usecase.spl", "use_cases")
checker.assign_module_layer("entity.spl", "entities")

# frameworks -> adapters (3->2): allowed
val v1 = checker.check_dependency("framework.spl", "adapter.spl")
expect(v1).to_be_nil()
# adapters -> use_cases (2->1): allowed
val v2 = checker.check_dependency("adapter.spl", "usecase.spl")
expect(v2).to_be_nil()
# use_cases -> entities (1->0): allowed
val v3 = checker.check_dependency("usecase.spl", "entity.spl")
expect(v3).to_be_nil()
```

</details>

#### Clean Architecture outward dependency denied

1. var checker = LayerChecker new
2. checker assign module layer
3. checker assign module layer
   - Expected: is_denied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(
    ["entities", "use_cases", "adapters", "frameworks"],
    LayerDirection.LowerToUpper
)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("entity.spl", "entities")
checker.assign_module_layer("framework.spl", "frameworks")
# entities (0) -> frameworks (3): outward = denied
val violation = checker.check_dependency("entity.spl", "framework.spl")
val is_denied = violation.?
expect(is_denied).to_equal(true)
```

</details>

### LayerChecker adjacent_only mode

#### allows adjacent layer dependency

1. var checker = LayerChecker new
2. checker assign module layer
3. checker assign module layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var layer = LayerDef(
    order: ["api", "app", "domain", "infra"],
    direction: LayerDirection.UpperToLower,
    allow_same_layer: true,
    allow_adjacent_only: true
)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("handler.spl", "api")
checker.assign_module_layer("service.spl", "app")
# api (0) -> app (1): adjacent = allowed
val violation = checker.check_dependency("handler.spl", "service.spl")
expect(violation).to_be_nil()
```

</details>

#### denies non-adjacent layer dependency

1. var checker = LayerChecker new
2. checker assign module layer
3. checker assign module layer
   - Expected: is_denied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var layer = LayerDef(
    order: ["api", "app", "domain", "infra"],
    direction: LayerDirection.UpperToLower,
    allow_same_layer: true,
    allow_adjacent_only: true
)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("handler.spl", "api")
checker.assign_module_layer("repo.spl", "domain")
# api (0) -> domain (2): skip = denied
val violation = checker.check_dependency("handler.spl", "repo.spl")
val is_denied = violation.?
expect(is_denied).to_equal(true)
```

</details>

#### same layer is still allowed in adjacent mode

1. var checker = LayerChecker new
2. checker assign module layer
3. checker assign module layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var layer = LayerDef(
    order: ["api", "app", "domain"],
    direction: LayerDirection.UpperToLower,
    allow_same_layer: true,
    allow_adjacent_only: true
)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("svc_a.spl", "app")
checker.assign_module_layer("svc_b.spl", "app")
val violation = checker.check_dependency("svc_a.spl", "svc_b.spl")
expect(violation).to_be_nil()
```

</details>

#### same layer denied when allow_same_layer is false

1. var checker = LayerChecker new
2. checker assign module layer
3. checker assign module layer
   - Expected: is_denied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var layer = LayerDef(
    order: ["api", "app", "domain"],
    direction: LayerDirection.UpperToLower,
    allow_same_layer: false,
    allow_adjacent_only: true
)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("svc_a.spl", "app")
checker.assign_module_layer("svc_b.spl", "app")
val violation = checker.check_dependency("svc_a.spl", "svc_b.spl")
val is_denied = violation.?
expect(is_denied).to_equal(true)
```

</details>

#### adjacent-only with LowerToUpper direction

1. var checker = LayerChecker new
2. checker assign module layer
3. checker assign module layer
4. checker assign module layer
   - Expected: is_denied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var layer = LayerDef(
    order: ["entities", "use_cases", "adapters", "frameworks"],
    direction: LayerDirection.LowerToUpper,
    allow_same_layer: true,
    allow_adjacent_only: true
)
var checker = LayerChecker.new(layer)
checker.assign_module_layer("framework.spl", "frameworks")
checker.assign_module_layer("adapter.spl", "adapters")
checker.assign_module_layer("entity.spl", "entities")

# frameworks (3) -> adapters (2): adjacent inward = allowed
val v1 = checker.check_dependency("framework.spl", "adapter.spl")
expect(v1).to_be_nil()
# frameworks (3) -> entities (0): skip inward = denied
val v2 = checker.check_dependency("framework.spl", "entity.spl")
val is_denied = v2.?
expect(is_denied).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mdsoc/layer_checker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- check_layer_dep
- LayerChecker construction
- LayerChecker assign_module_layer
- LayerChecker check_dependency
- LayerChecker detect_layer_cycles
- LayerChecker bypass grants
- LayerChecker bypass non-transitive
- LayerChecker generate_bypass_report
- LayerChecker with LowerToUpper direction
- LayerChecker adjacent_only mode

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 43 |
| Active scenarios | 43 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
