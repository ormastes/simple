# Lifecycle Persistence Model

Simple models lifecycle persistence with the ordinary language. There are no
`life`, `virtual life`, `transition`, or `recovery` declarations.

## Import

```simple
use std.lifecycle_persistence.{
    LifecycleEdge,
    LifecycleGraph,
    LifecycleLevel,
    lifecycle_graph_validate
}
```

## Define and validate a graph

```simple
fn service_graph() -> LifecycleGraph:
    LifecycleGraph(
        levels: [
            LifecycleLevel(id: 0, name: "call"),
            LifecycleLevel(id: 1, name: "process")
        ],
        edges: [LifecycleEdge(shorter: 0, longer: 1)]
    )

val result = lifecycle_graph_validate(service_graph())
if not result.valid:
    error("invalid lifecycle metadata: {result.detail}")
```

An edge points from shorter survival to longer survival. A strong dependency is
allowed only when its lifecycle is equal to or reachable from the owner's
lifecycle.

## Transition and recovery metadata

Construct `LifecycleTransition` and `RecoveryRegistration` with direct struct
constructors inside ordinary functions. Validators reject unknown boundaries,
empty policy/function names, and non-positive recovery schemas.

Recovery algorithms remain ordinary Simple functions returning typed results.
The model contains no storage I/O and makes no crash-consistency claim.

## Identity and placement

Do not persist direct pointers, runtime `+T` handles, or the frozen
snapshot-local `common.structural.identity.EntityRef`. Reuse or distinctly wrap
the durable `EntityKey` owner and validate compatibility during activation.

Use existing `@section` source syntax and linker/board SDN for physical
placement and retention. Product integration must separately prove real
storage, restart, boot, power-cut, and formal-verification claims.

## Strictness

Select existing profiles with `@lint_profile(...)`, `--profile`, or project
configuration. Current names are `moderate`, `strict`, `robust`, and `critical`.
Selecting a profile does not by itself prove persistence correctness.

## Evidence

The focused model scenario is
`test/03_system/feature/language/robust_lifecycle_persistence_spec.spl`; its
mirrored operator manual is under `doc/06_spec/03_system/feature/language/`.

