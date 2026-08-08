# Simple Robust Lifecycle Persistence Design

**Status:** Selected convention-aligned design  
**Date:** 2026-08-04  
**Supersedes:** the custom-grammar proposal preserved at
`doc/01_research/domain/language/lifecycle/robust_lifecycle_persistence_research_synthesis_2026-08-04.md`

## Decision

Robust lifecycle persistence uses current Simple constructs. It adds a small
pure-Simple model and validators, not lexer, parser, AST, HIR, MIR, or keyword
changes.

The following proposed declarations are removed:

- `life Name:`
- `virtual life Name:`
- `transition Name:`
- `recovery Name for Type:`

Their information is ordinary data. Recovery behavior remains ordinary Simple
functions and state machines. Physical durability remains linker/board SDN plus
the existing `@section` attribute.

## Current syntax contract

Examples in this design use only current conventions:

- `val` for immutable bindings;
- `Type<T>` for generics and `[T]` for arrays;
- direct struct construction such as `LifecycleEdge(...)`;
- fully qualified enum variants;
- `if val` for optional binding;
- ordinary functions for configuration values;
- `Result<T, E>` for fallible behavior;
- current strictness profiles: `moderate`, `strict`, `robust`, and `critical`.

No lifecycle-specific attribute is required by the initial model. `@section`
continues to express source placement; SDN expresses physical retention.

## Typed model

Lifecycle levels are stable integer identifiers. Products define readable
constants without extending enum syntax:

```simple
val LIFE_CALL: i64 = 0
val LIFE_PROCESS: i64 = 1
val LIFE_WARM_BOOT: i64 = 2
val LIFE_POWER_LOSS: i64 = 3

fn device_lifecycle_graph() -> LifecycleGraph:
    LifecycleGraph(
        levels: [
            LifecycleLevel(id: LIFE_CALL, name: "call"),
            LifecycleLevel(id: LIFE_PROCESS, name: "process"),
            LifecycleLevel(id: LIFE_WARM_BOOT, name: "warm_boot"),
            LifecycleLevel(id: LIFE_POWER_LOSS, name: "power_loss")
        ],
        edges: [
            LifecycleEdge(shorter: LIFE_CALL, longer: LIFE_PROCESS),
            LifecycleEdge(shorter: LIFE_PROCESS, longer: LIFE_WARM_BOOT),
            LifecycleEdge(shorter: LIFE_WARM_BOOT, longer: LIFE_POWER_LOSS)
        ]
    )
```

An edge means the `longer` level survives every boundary represented by the
`shorter` level. The validator checks uniqueness, known endpoints, and cycles.

## Dependency rule

For an owner at lifecycle `A` and a strong dependency at lifecycle `B`, the
dependency is safe only when `A == B` or the graph contains a path `A -> B`.

Shorter-lived values remain explicit in product data through ordinary wrappers
or identifiers. The initial library does not prescribe a universal wrapper set;
products may define `Rebuild<T>`, `Rebind<T>`, or environment references when
they need those semantics.

## Transition metadata

A transition is an ordinary value:

```simple
fn sudden_power_loss() -> LifecycleTransition:
    LifecycleTransition(
        name: "sudden_power_loss",
        boundary: LIFE_POWER_LOSS,
        kind: TransitionKind.Crash,
        volatile_policy: "lose",
        retained_policy: "platform_retention",
        persistent_policy: "storage_failure_model",
        environment_policy: "may_change",
        restart_entry: "reset_vector"
    )
```

The product can serialize equivalent configuration in SDN. Source functions are
preferred for freestanding defaults because complex module-global initializers
are not reliable on every kernel path.

## Recovery registration

Registration binds names of ordinary product functions; it does not introduce a
recovery mini-language:

```simple
fn namespace_recovery_registration() -> RecoveryRegistration:
    RecoveryRegistration(
        name: "namespace_recovery",
        state_type: "NamespaceState",
        lifecycle: LIFE_POWER_LOSS,
        schema: 3,
        codec: "namespace_codec",
        validate: "validate_namespace",
        migrate: "migrate_namespace",
        recover: "recover_namespace",
        clean_start: "clean_namespace",
        reconcile: "reconcile_namespace",
        activate: "activate_namespace"
    )
```

The registered functions use normal signatures:

```simple
fn recover_namespace(
    decoded: DecodedNamespace,
    environment: NamespaceEnvironment
) -> Result<ValidatedNamespace, RecoveryFault>:
    val migrated = migrate_namespace(decoded)?
    val checked = validate_namespace(migrated)?
    reconcile_namespace(checked, environment)
```

## Persistent identity

The repository already owns a frozen snapshot-local `EntityRef` and a durable
`EntityKey` under `common.structural.identity`. This design does not redefine
`EntityRef` and does not serialize runtime `+T` handles or direct pointers as
persistent identity.

Product-specific type safety may wrap `EntityKey` in a distinctly named struct:

```simple
struct NamespaceEntityKey:
    key: EntityKey

fn namespace_entity_key(key: EntityKey) -> NamespaceEntityKey:
    NamespaceEntityKey(key: key)
```

Resolution after restart must validate artifact/schema compatibility before
producing a current runtime handle.

## Physical placement

Source uses the existing section attribute:

```simple
@section(".persist.namespace")
var namespace_root: NamespaceState
```

Board/linker SDN owns retention and initialization policy:

```sdn
[sections.persist_namespace]
input = ".persist.namespace"
region = "metadata_flash"
initialize = "validate_then_recover"
```

The platform integration must reject a source lifecycle claim that exceeds the
selected region's durability. That cross-check belongs after the pure model,
not in new source grammar.

## Strictness integration

Lifecycle diagnostics use the existing lint configuration:

```simple
@lint_profile(robust)
```

`moderate`, `strict`, `robust`, and `critical` retain their documented meaning.
The feature adds lint rules only when implemented checks exist; profile names do
not themselves prove crash consistency or formal correctness.

## Validation API

The initial public functions are:

- `lifecycle_graph_validate(graph)`
- `lifecycle_level_known(graph, id)`
- `lifecycle_reaches(graph, shorter, longer)`
- `lifecycle_dependency_allowed(graph, owner, dependency)`
- `lifecycle_transition_validate(graph, transition)`
- `recovery_registration_validate(graph, registration)`

Validation returns a typed result containing a stable error code and detail.
There are no hardcoded pass values, raw runtime calls, or hidden defaults.

## Error handling

The validator distinguishes empty or duplicate lifecycle levels, unknown edge
endpoints, graph cycles, unknown transition/recovery boundaries, empty transition
fields, non-positive recovery schema, and missing recovery function bindings.
The first error is deterministic for the same input.

## Testing boundary

Focused tests cover valid and invalid graphs, both dependency directions,
transition metadata, and recovery registration. These tests prove the typed
model only. Product storage, reboot, power-cut, linker, and formal-proof claims
require separate system evidence.

## Implementation sequence

1. Add the pure common model and validation functions.
2. Export the model through the default `nogc_async_mut` stdlib family.
3. Add focused unit and SPipe scenarios with requirement traceability.
4. Generate and review the mirrored scenario manual.
5. Run changed-file lint, duplicate/stub guards, and direct runtime-access guards.
6. Add platform adapters only in later product-owned lanes.

## Acceptance mapping

| Requirement | Evidence |
|---|---|
| REQ-001..003 | No grammar/compiler changes; current-syntax source and docs |
| REQ-004..006 | Pure model validators and focused tests |
| REQ-007..008 | Existing identity-owner reuse and identity review |
| REQ-009 | Existing `@section` plus SDN design boundary |
| REQ-010 | Existing strictness profile documentation and lint invocation |
| REQ-011 | Ordinary recovery function example and product boundary |
| REQ-012 | Unit and SPipe scenario results |

