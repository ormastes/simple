# AOP Architecture Rules Specification

> forbid pc{ import(from_pattern, to_pattern) } "Error message"

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
| Updated | 2026-08-26 |
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

- forbids importing test internals in production


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("forbids importing test internals in production")
# This rule prevents production code from importing test helpers
forbid pc{ import(test.internal.*) } "Production code cannot import test internals"

# Rule declared successfully
expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### forbids importing implementation details

- forbids importing implementation details


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("forbids importing implementation details")
forbid pc{ import(*.internal.*) } "Cannot import internal modules directly"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### dependency rules

#### forbids domain depending on infrastructure

- forbids domain depending on infrastructure


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("forbids domain depending on infrastructure")
# Classic clean architecture constraint
forbid pc{ depend(within(domain.**), within(infrastructure.**)) } "Domain layer cannot depend on infrastructure"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### forbids circular dependencies

- forbids circular dependencies


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("forbids circular dependencies")
forbid pc{ depend(within(module_a.**), within(module_b.**)) & depend(within(module_b.**), within(module_a.**)) } "Circular dependency detected"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### usage rules

#### forbids using Container in domain

- forbids using Container in domain


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("forbids using Container in domain")
forbid pc{ use(Container) & within(domain.**) } "Domain should not use DI Container directly"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### forbids using deprecated types

- forbids using deprecated types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("forbids using deprecated types")
forbid pc{ use(LegacyService) } "LegacyService is deprecated, use NewService"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### config rules

#### forbids test config in release

- forbids test config in release


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("forbids test config in release")
forbid pc{ config("profiles.test") & attr(release) } "Cannot use test profile in release build"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

### Architecture Allow Rules

#### selective allows

#### allows api to depend on core

- allows api to depend on core


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows api to depend on core")
# First forbid broad dependency
forbid pc{ depend(within(api.**), within(**)) } "API should not depend on anything"

# Then allow specific exception
allow pc{ depend(within(api.**), within(core.**)) } "API can depend on core"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### allows test code to use internal modules

- allows test code to use internal modules


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows test code to use internal modules")
forbid pc{ import(*.internal.*) } "Cannot import internal modules"
allow pc{ import(*.internal.*) & within(test.**) } "Tests can import internals"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### priority-based overrides

#### allow with higher priority overrides forbid

- allow with higher priority overrides forbid


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allow with higher priority overrides forbid")
# Rules are resolved by priority
forbid pc{ use(DebugHelper) } "DebugHelper forbidden" # priority default: 0
allow pc{ use(DebugHelper) & within(debug.**) } "Debug module can use DebugHelper" # priority: 10

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

### Layered Architecture Constraints

#### three-layer architecture

#### defines presentation layer constraints

- defines presentation layer constraints


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines presentation layer constraints")
# Presentation can only depend on application layer
forbid pc{ depend(within(presentation.**), within(domain.**)) } "Presentation cannot access domain directly"
forbid pc{ depend(within(presentation.**), within(infrastructure.**)) } "Presentation cannot access infrastructure"
allow pc{ depend(within(presentation.**), within(application.**)) } "Presentation depends on application"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### defines application layer constraints

- defines application layer constraints


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines application layer constraints")
# Application can depend on domain
forbid pc{ depend(within(application.**), within(infrastructure.**)) } "Application cannot depend on infrastructure"
allow pc{ depend(within(application.**), within(domain.**)) } "Application depends on domain"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### defines domain layer constraints

- defines domain layer constraints


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines domain layer constraints")
# Domain is the core, depends on nothing
forbid pc{ depend(within(domain.**), within(application.**)) } "Domain cannot depend on application"
forbid pc{ depend(within(domain.**), within(infrastructure.**)) } "Domain cannot depend on infrastructure"
forbid pc{ depend(within(domain.**), within(presentation.**)) } "Domain cannot depend on presentation"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### hexagonal architecture

#### enforces port-adapter boundaries

- enforces port-adapter boundaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enforces port-adapter boundaries")
# Adapters implement ports, core doesn't know about adapters
forbid pc{ depend(within(core.**), within(adapters.**)) } "Core cannot depend on adapters"
forbid pc{ import(adapters.*.internal.*) } "Cannot import adapter internals"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

### Module Boundary Rules

#### internal modules

#### forbids importing internal submodules

- forbids importing internal submodules


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("forbids importing internal submodules")
forbid pc{ import(*.internal.*) } "Internal modules are not public API"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### requires using public facade

- requires using public facade


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires using public facade")
# Force usage through public module
forbid pc{ import(services.user.repository) } "Use services.user instead"
allow pc{ import(services.user) } "Public facade allowed"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### export restrictions

#### forbids exporting internal types

- forbids exporting internal types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("forbids exporting internal types")
forbid pc{ export(*Internal) } "Types ending in Internal should not be exported"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

### Security Architecture Rules

#### credential access

#### restricts credential usage

- restricts credential usage


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("restricts credential usage")
# Only auth module can access credentials
forbid pc{ use(Credentials) & !within(auth.**) } "Only auth module can use Credentials"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### forbids storing secrets in plain text

- forbids storing secrets in plain text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("forbids storing secrets in plain text")
forbid pc{ use(PlainTextSecret) } "Use EncryptedSecret instead of PlainTextSecret"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### network boundaries

#### restricts direct network access

- restricts direct network access


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("restricts direct network access")
forbid pc{ use(HttpClient) & within(domain.**) } "Domain should not make HTTP calls directly"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

### Test Isolation Rules

#### test-only code

#### forbids mock in production

- forbids mock in production


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("forbids mock in production")
forbid pc{ use(Mock*) & !within(test.**) } "Mocks can only be used in test code"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### forbids test utilities in production

- forbids test utilities in production


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("forbids test utilities in production")
forbid pc{ import(test.helpers.*) & !within(test.**) } "Test helpers cannot be used in production"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### test profile restrictions

#### forbids test profile in release

- forbids test profile in release


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("forbids test profile in release")
forbid pc{ config("profile.test") & attr(release) } "Cannot use test profile in release"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

### Architecture Rule Diagnostics

#### violation messages

#### provides actionable error message

- provides actionable error message


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("provides actionable error message")
# Good error messages explain:
# 1. What is forbidden
# 2. Why it's forbidden
# 3. What to do instead
forbid pc{ use(OldApi) } "OldApi is deprecated since v2.0. Use NewApi.method() instead. See migration guide: /docs/migration/v2"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### identifies violation location

- identifies violation location


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identifies violation location")
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

- combines multiple conditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("combines multiple conditions")
forbid pc{ (depend(within(a.**), within(b.**)) | depend(within(a.**), within(c.**))) & !attr(allowed_dependency) } "Module A has restricted dependencies"

expect("architecture rule declaration reached").to_contain("rule")
```

</details>

#### uses negation for exceptions

- uses negation for exceptions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses negation for exceptions")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d19eb552e8cb39b0163c8bd183a9cade42ac3890fa043ba1c853226679b56016`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d19eb552e8cb39b0163c8bd183a9cade42ac3890fa043ba1c853226679b56016`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d19eb552e8cb39b0163c8bd183a9cade42ac3890fa043ba1c853226679b56016`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/aop_architecture_rules_spec.spl
mirror: doc/06_spec/03_system/feature/usage/aop_architecture_rules_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/aop_architecture_rules_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/aop_architecture_rules_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/aop_architecture_rules_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'forbids importing test internals in production' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/aop_architecture_rules_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'forbids importing implementation details' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/aop_architecture_rules_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'forbids domain depending on infrastructure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
