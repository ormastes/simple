# Mission-Critical rt(hal) Compile and Memory Policy

Purpose: verify Critical defaults, bounded configuration, sealed archive policy, and fail-closed allocation/legacy contracts. Audience: compiler and safety reviewers.

Source: `test/03_system/runtime/hal_mission_critical_policy_spec.spl`  
Evidence class: executable source contract  
Current execution status: **PENDING/BLOCKED** — no admitted self-hosted compiler is available; warning-to-error migration timing is not claimed complete.

## Preconditions

The declaration must name an operation and use bounded schemas/capacities. Mission-critical entry closures require sealed archives and zero allocations after initialization.

## Operator workflow

1. Parse an unqualified and an explicit declaration.
2. Capture the canonical compile contract.
3. Compare assurance and capacity bounds.
4. Inject missing rationale, obsolete field, over-capacity value, and post-seal allocation.
5. Verify deterministic diagnostics and rejection.

## Scenarios

- Unqualified `rt(hal)` defaults to Critical, all providers, and sealed archive linkage.
- Explicit Verified configuration remains bounded.
- Lower assurance without rationale is rejected.
- Unknown/obsolete fields and values above 4 MiB are rejected.
- Any post-initialization allocation rejects the sealed storage receipt.

## Acceptance boundary

The executable contract covers new/changed-code errors. Repository-wide legacy warning inventory, next-release escalation, compatibility-shim removal, and measured allocation evidence remain external release gates and are pending.

## Traceability

REQ-009 through REQ-012 and REQ-019; NFR-005, NFR-006, and NFR-009.

## Executable source

The complete executable source remains in `test/03_system/runtime/hal_mission_critical_policy_spec.spl`.
