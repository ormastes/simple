<!-- codex-research -->
# Feature Requirement Options: IDE Plugin Architecture

## Option A: Manifest Registry Only

Description: add a manifest and contribution registry, then migrate Office feature reports/catalogs onto it.

Pros:
- Smallest implementation slice.
- Makes plugins discoverable without changing runtime execution.
- Low risk for existing Office tools.

Cons:
- Does not solve DI, lifecycle, or aspect hooks yet.
- Plugin behavior remains scattered.

Effort: M, 8-12 files.

## Option B: Plugin Kernel With DI

Description: add manifest registry, activation events, host routing, and a scoped service container for dependency injection.

Pros:
- Gives Office and IDE plugins a real runtime contract.
- Keeps sibling plugins decoupled through service tokens.
- Matches VS Code and Eclipse architecture lessons while staying Simple-native.

Cons:
- Requires migration planning for existing Office commands and catalogs.
- Needs capability validation and lifecycle tests.

Effort: L, 18-28 files.

## Option C: Plugin Kernel With DI And AOP

Description: implement Option B plus ordered aspect chains for command, document, render, diagnostics, telemetry, undo/redo, and persistence hooks.

Pros:
- Best fit for Libre-level Office hardening where many concerns cross Writer, Slides, Sheets, Diagram, Designer, and DB Admin.
- Makes plugin connection explicit and testable.
- Gives MDSOC virtual capsules a concrete runtime weaving model.

Cons:
- Highest design and verification burden.
- Aspect ordering and failure semantics must be strict to avoid hard-to-debug behavior.

Effort: XL, 35-55 files.

## Recommendation

Choose Option C as the target architecture, but implement it in slices: A first, B second, AOP hooks third.

