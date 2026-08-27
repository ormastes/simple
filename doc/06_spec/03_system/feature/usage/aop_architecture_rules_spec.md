# AOP Architecture Rules Specification

> forbid pc{ import(from_pattern, to_pattern) } "Error message"

<!-- sdn-diagram:id=aop_architecture_rules_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aop_architecture_rules_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aop_architecture_rules_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aop_architecture_rules_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# AOP Architecture Rules Specification

forbid pc{ import(from_pattern, to_pattern) } "Error message"

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AOP-ARCH-001 to #AOP-ARCH-010 |
| Category | Language |
| Status | Implemented |
| Source | `test/03_system/feature/usage/aop_architecture_rules_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Forbid pattern with error message
forbid pc{ import(from_pattern, to_pattern) } "Error message"
forbid pc{ depend(from_pattern, to_pattern) } "Error message"

# Allow pattern (exceptions)
allow pc{ depend(within(api.**), within(core.**)) } "Allowed exception"
```

## Architecture Selectors

| Selector | Description |
|----------|-------------|
| import(from, to) | Match import statements |
| depend(from, to) | Match module dependencies |
| use(pattern) | Match type/function usage |
| export(pattern) | Match exported symbols |
| config(string) | Match configuration values |

## Scenarios

### Architecture Forbid Rules

#### import rules

#### forbids importing test internals in production

1. forbid pc{ import


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This rule prevents production code from importing test helpers
forbid pc{ import(test.internal.*) } "Production code cannot import test internals"

# Rule declared successfully
expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### forbids importing implementation details

1. forbid pc{ import


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
forbid pc{ import(*.internal.*) } "Cannot import internal modules directly"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### dependency rules

#### forbids domain depending on infrastructure

1. forbid pc{ depend


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Classic clean architecture constraint
forbid pc{ depend(within(domain.**), within(infrastructure.**)) } "Domain layer cannot depend on infrastructure"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### forbids circular dependencies

1. forbid pc{ depend


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
forbid pc{ depend(within(module_a.**), within(module_b.**)) & depend(within(module_b.**), within(module_a.**)) } "Circular dependency detected"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### usage rules

#### forbids using Container in domain

1. forbid pc{ use


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
forbid pc{ use(Container) & within(domain.**) } "Domain should not use DI Container directly"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### forbids using deprecated types

1. forbid pc{ use


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
forbid pc{ use(LegacyService) } "LegacyService is deprecated, use NewService"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### config rules

#### forbids test config in release

1. forbid pc{ config


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
forbid pc{ config("profiles.test") & attr(release) } "Cannot use test profile in release build"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

### Architecture Allow Rules

#### selective allows

#### allows api to depend on core

1. forbid pc{ depend
2. allow pc{ depend


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# First forbid broad dependency
forbid pc{ depend(within(api.**), within(**)) } "API should not depend on anything"

# Then allow specific exception
allow pc{ depend(within(api.**), within(core.**)) } "API can depend on core"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### allows test code to use internal modules

1. forbid pc{ import
2. allow pc{ import


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
forbid pc{ import(*.internal.*) } "Cannot import internal modules"
allow pc{ import(*.internal.*) & within(test.**) } "Tests can import internals"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### priority-based overrides

#### allow with higher priority overrides forbid

1. forbid pc{ use
2. allow pc{ use


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rules are resolved by priority
forbid pc{ use(DebugHelper) } "DebugHelper forbidden" # priority default: 0
allow pc{ use(DebugHelper) & within(debug.**) } "Debug module can use DebugHelper" # priority: 10

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

### Layered Architecture Constraints

#### three-layer architecture

#### defines presentation layer constraints

1. forbid pc{ depend
2. forbid pc{ depend
3. allow pc{ depend


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Presentation can only depend on application layer
forbid pc{ depend(within(presentation.**), within(domain.**)) } "Presentation cannot access domain directly"
forbid pc{ depend(within(presentation.**), within(infrastructure.**)) } "Presentation cannot access infrastructure"
allow pc{ depend(within(presentation.**), within(application.**)) } "Presentation depends on application"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### defines application layer constraints

1. forbid pc{ depend
2. allow pc{ depend


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Application can depend on domain
forbid pc{ depend(within(application.**), within(infrastructure.**)) } "Application cannot depend on infrastructure"
allow pc{ depend(within(application.**), within(domain.**)) } "Application depends on domain"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### defines domain layer constraints

1. forbid pc{ depend
2. forbid pc{ depend
3. forbid pc{ depend


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Domain is the core, depends on nothing
forbid pc{ depend(within(domain.**), within(application.**)) } "Domain cannot depend on application"
forbid pc{ depend(within(domain.**), within(infrastructure.**)) } "Domain cannot depend on infrastructure"
forbid pc{ depend(within(domain.**), within(presentation.**)) } "Domain cannot depend on presentation"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### hexagonal architecture

#### enforces port-adapter boundaries

1. forbid pc{ depend
2. forbid pc{ import


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Adapters implement ports, core doesn't know about adapters
forbid pc{ depend(within(core.**), within(adapters.**)) } "Core cannot depend on adapters"
forbid pc{ import(adapters.*.internal.*) } "Cannot import adapter internals"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

### Module Boundary Rules

#### internal modules

#### forbids importing internal submodules

1. forbid pc{ import


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
forbid pc{ import(*.internal.*) } "Internal modules are not public API"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### requires using public facade

1. forbid pc{ import
2. allow pc{ import


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Force usage through public module
forbid pc{ import(services.user.repository) } "Use services.user instead"
allow pc{ import(services.user) } "Public facade allowed"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### export restrictions

#### forbids exporting internal types

1. forbid pc{ export


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
forbid pc{ export(*Internal) } "Types ending in Internal should not be exported"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

### Security Architecture Rules

#### credential access

#### restricts credential usage

1. forbid pc{ use


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Only auth module can access credentials
forbid pc{ use(Credentials) & !within(auth.**) } "Only auth module can use Credentials"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### forbids storing secrets in plain text

1. forbid pc{ use


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
forbid pc{ use(PlainTextSecret) } "Use EncryptedSecret instead of PlainTextSecret"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### network boundaries

#### restricts direct network access

1. forbid pc{ use


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
forbid pc{ use(HttpClient) & within(domain.**) } "Domain should not make HTTP calls directly"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

### Test Isolation Rules

#### test-only code

#### forbids mock in production

1. forbid pc{ use


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
forbid pc{ use(Mock*) & !within(test.**) } "Mocks can only be used in test code"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### forbids test utilities in production

1. forbid pc{ import


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
forbid pc{ import(test.helpers.*) & !within(test.**) } "Test helpers cannot be used in production"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### test profile restrictions

#### forbids test profile in release

1. forbid pc{ config


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
forbid pc{ config("profile.test") & attr(release) } "Cannot use test profile in release"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

### Architecture Rule Diagnostics

#### violation messages

#### provides actionable error message

1. forbid pc{ use


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Good error messages explain:
# 1. What is forbidden
# 2. Why it's forbidden
# 3. What to do instead
forbid pc{ use(OldApi) } "OldApi is deprecated since v2.0. Use NewApi.method() instead. See migration guide: /docs/migration/v2"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### identifies violation location

1. forbid pc{ depend


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The compiler should report:
# - File and line of violation
# - The rule that was violated
# - Suggested fix
forbid pc{ depend(within(ui.**), within(db.**)) } "UI layer cannot access database directly. Inject a repository interface instead."

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

### Architecture Rule Composition

#### complex patterns

#### combines multiple conditions

1. forbid pc{


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
forbid pc{ (depend(within(a.**), within(b.**)) | depend(within(a.**), within(c.**))) & !attr(allowed_dependency) } "Module A has restricted dependencies"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### uses negation for exceptions

1. forbid pc{ export


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Forbid everything except specific patterns
forbid pc{ export(*) & !export(*Service) & !export(*Repository) & within(core.**) } "Core should only export Services and Repositories"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
