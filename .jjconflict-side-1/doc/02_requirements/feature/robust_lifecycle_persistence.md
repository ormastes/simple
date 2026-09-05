# Robust Lifecycle Persistence Requirements

**Status:** Selected by the user on 2026-08-04  
**Selection:** Existing-Simple library model; no lifecycle-specific grammar

## Requirements

- REQ-001: Lifecycle and persistence metadata shall be expressible with current Simple `enum`, `struct`, `trait`, function, constructor, generic, attribute, and SDN syntax.
- REQ-002: The feature shall add no `life`, `virtual life`, `transition`, or `recovery ... for ...` declarations and no corresponding contextual or reserved keywords.
- REQ-003: The feature shall add no lifecycle-only field syntax or attributes when an ordinary wrapper type or registration value expresses the same contract.
- REQ-004: Lifecycle order shall be represented as data and validated as an acyclic directed graph.
- REQ-005: A strong dependency from an owner to a dependency shall be valid only when the dependency survives every boundary the owner survives.
- REQ-006: Transition and recovery policy shall be typed library values produced by ordinary Simple functions.
- REQ-007: Persistent identity shall reuse the repository's durable identity vocabulary and shall not redefine the existing snapshot-local `EntityRef` contract.
- REQ-008: Runtime handles, direct pointers, and snapshot-local entity references shall not be presented as reboot-stable persistent identities.
- REQ-009: Physical placement and retention details shall remain in linker/board SDN and existing `@section` syntax.
- REQ-010: Strictness shall use the current `moderate`, `strict`, `robust`, and `critical` profiles selected through existing lint configuration.
- REQ-011: Recovery algorithms shall remain ordinary Simple functions and state machines.
- REQ-012: Focused executable tests shall cover graph validity, dependency ordering, transition metadata, and recovery registration validation.

## Exclusions

- Parser, lexer, AST, HIR, MIR, or keyword additions.
- A lifecycle mini-language.
- A second identity type named `EntityRef`.
- Backend-specific persistence engines, crash-consistency proofs, and product-specific boot integration in the first implementation.

