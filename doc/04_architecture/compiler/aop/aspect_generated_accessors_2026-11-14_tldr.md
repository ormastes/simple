# Aspect-generated accessors — TLDR

[Full contract](aspect_generated_accessors_2026-11-14.md). Accepted architecture with staged source implementation; public/runtime support remains unqualified.

- Generate typed internal get/set helpers only for explicitly requested generation or matching field aspects. Keep existing field layout, access checks and RHS-before-receiver assignment order.
- Freeze named aspect identity and token-aware selector handling first (P0). Keep get/set rejection until actual typed lowering and consumers exist.
- P1 admits direct nonvolatile/non-atomic stored bool/integer fields on resolved identity-bearing class references. Parameterless advice stays distinct from the typed internal helper ABI.
- One frozen helper key has one deterministic companion emission owner and compiler-private cross-module linkage. Include field/instantiation, physical ABI, provider and complete ordered advice in cache identity.
- Getter loads once before after_success and returns that retained result, even when advice mutates the field. Preserve receiver/result liveness. Setter commits before after_success; advice failures follow existing semantics.
- No selected aspect and no generation request means unchanged field lowering, helper inventory and dependencies. Exclude generated helpers from ordinary execution matching to prevent duplicate events.
- P2/P3 still owe value/nested/indexed/RMW places, borrowed/move/atomic fields, computed/forwarded/read-only properties, SPL/SDN/interpreter parity, caches and tooling. A scalar pilot is not completion.

Source owners: frontend advice/parser; HIR resolved field/place facts; MIR field read/assignment and existing advice injection; schema-generated artifact metadata. Coordinate node-storage ownership before editing its files.

Acceptance: full contract G1–G14 includes operand order, actual object mutation, visibility, zero-change off baseline, single helper emission, captured-value/liveness and native/interpreter parity. These are planned tests, not passes.

Current [producer checkpoint](../../../09_report/compiler/aspect_accessor_producer_checkpoint_2026-11-14.md) connects source inventory, authenticated providers, named handlers, coordinator-reserved canonical type IDs and real MIR consumers. Native and cache/transport qualification remain open; public get/set stays rejected.
