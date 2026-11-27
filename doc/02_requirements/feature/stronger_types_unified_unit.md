# Requirements — Stronger Types: Unified `unit`, Effects, Protocol States, LSP

**Date:** 2026-11-05
**Feature:** `stronger_types_unified_unit`
**Selection record:** Requirement options were generated and decided in `doc/05_design/stronger_types_unified_unit.md` §1.1 (properties ST-01..ST-11) and §3.1 (merger). The user directed implementation of that plan ("impl the simple hardening plan and land"). Rejected alternatives recorded in the design: keeping `unit`/`newunit`/`newtype` as three permanent keywords; introducing `refined`/`state`/`session`/`capability` keywords or mandatory `requires`/`no_panic` annotations; adding a parallel effect system. These are not archived elsewhere.
**Sources:** `doc/01_research/local/stronger_types_unified_unit.md`, `doc/01_research/domain/stronger_types_unified_unit.md`.

## Functional requirements

| ID | Requirement | Acceptance test IDs |
|---|---|---|
| REQ-UNIT-01 | `unit` is the sole declaration keyword for nominal IDs, nominal wrappers, measurement families, refined values, aliases, and zero-payload state markers. Forms: `unit Name: T as suffix`, `unit Name: T` (+ invariant body), `unit Name(base: T):` scales, `unit Name(base: T) = dim-expr:`, `unit Name = ExistingType`, `unit Name`. | UNIT-01..UNIT-05, PARSE-01..PARSE-02 |
| REQ-UNIT-02 | Legacy `newunit`/`newtype` spellings remain accepted during a bounded compatibility window, lower to the same canonical representation, and emit a deprecation diagnostic with a semantics-preserving fix once equivalence is established. | UNIT-01, UNIT-02, LSP-04 |
| REQ-UNIT-03 | Nominal identity, alias identity, dimensions, predicates, and state markers remain distinct compiler facts: nominals with identical representation are not interchangeable; aliases resolve to the target identity; representation equality never permits state-marker casts. | UNIT-03, UNIT-08, STATE-01 |
| REQ-UNIT-04 | Refined values (`unit Port: u16:` + invariant) enforce the predicate at construction and mutation: no unchecked constructor for unknown values; a checked constructor (`try_from`-style) returns a typed error; invalid constants are rejected at compile time when provable. | UNIT-06, UNIT-07, INV-01 |
| REQ-UNIT-05 | Measurement dimensions normalize in compiler metadata; same-dimension conversions succeed under documented rules; incompatible dimensions and unrelated nominal IDs are compile errors; inexact/narrowing/overflow conversions are diagnosed or typed errors, never silent. | UNIT-04, UNIT-05 |
| REQ-UNIT-06 | Declared-type metadata uses scalable storage (no fixed 16-slot cap); ABI size/alignment derive from the target layout engine, not from byte size. | UNIT-09, UNIT-10 |
| REQ-EFF-01 | Effect inference is fail-closed for unknowns: unhandled HIR kinds, failed callee synthesis, and unresolved callees produce an explicit `unknown`/incomplete marker rather than an empty or fabricated-complete row. | EFF-03 |
| REQ-EFF-02 | Effect rows are sound upper bounds through direct, recursive, generic, closure, method, and FFI calls; closure creation effects are separate from latent invocation effects; `Throws` comparisons preserve payload identity or a sound upper bound. | EFF-02, EFF-04 |
| REQ-EFF-03 | I/O and allocation effects are attributed from resolved operations, not names; backend-introduced allocation/cleanup is included in summaries. | EFF-01, EFF-05 |
| REQ-EFF-04 | Per-function effect summaries are cached and published for LSP/CLI/MCP consumption with completeness status (complete / incomplete / stale / target-dependent). | EFF-03, LSP-01, CLI-01 |
| REQ-CHAN-01 | Channels bind a single payload type at creation; `Sender<T>`/`Receiver<T>` (or resource-bound `Channel<T>`) endpoints created together share payload type and transfer policy; per-call re-typing of `send`/`recv` is rejected for new code. | CHAN-01 |
| REQ-CHAN-02 | Send admission results are observable: closed/full/rejected sends return typed errors carrying message ownership where safe; no silent discard. | CHAN-02, CHAN-03 |
| REQ-STATE-01 | Local resource lifecycle (TCP as first owner) encodes legal transitions with ownership: consuming transitions remove permissions (e.g. `shutdown_write` removes write permission), use-after-consume and double transitions fail statically, failed transitions define remaining ownership. | STATE-01, STATE-03 |
| REQ-SESS-01 | Optional finite session protocol descriptors (generic continuation types) validate message order, direction, payload, and branching at compile time; recursion uses bounded finite graph processing. | SESSION-01, SESSION-02 |
| REQ-SESS-02 | Cancellation before/after commit and partial I/O produce declared owned continuations; no automatic replay after commit. | SESSION-03 |
| REQ-CAP-01 | Alias/capture constraints conservatively invalidate permissions across transitions and suspension; unsupported revocation cases are rejected or downgraded, never silently accepted. | STATE-02 |
| REQ-MODE-01 | High-overhead verification (deep refinement solvers, whole-program protocol/alias analysis, expensive MIR translation validation, instrumentation) runs only in `debug`, `invest`, and `ci` modes with explicit budgets; normal/release builds never launch them automatically. | MODE-01, MODE-02, MIR-01 |
| REQ-MODE-02 | Cheap mandatory checks (nominal/dimension matching, ownership/state rules, conservative effect bounds, boundary validation, lightweight MIR structural verification) cannot be disabled by mode selection. | MODE-01, MIR-01 |
| REQ-ABI-01 | Unit erasure preserves scalar layout but never validates foreign values; refinements are validated when crossing untrusted boundaries; FFI/dynload contracts carry type/effect/state commitments checked at admission. | FFI-01, FFI-02 |
| REQ-LSP-01 | LSP/CLI/MCP share one semantic service: unit hover (role, representation, suffix, dimension, predicate), effect hover/provenance with completeness, typestate hover, invariant classification, and versioned migration edit plans; previews are read-only; stale plans fail validation. | LSP-01..LSP-04, CLI-01 |
| REQ-TOOL-01 | `simple inspect` (type/effects/state) and `simple refactor unit` commands plus MCP tool entries route through the same providers as LSP, emitting the same diagnostic/edit-plan identifiers. | CLI-01 |
| REQ-MIG-01 | All source migrations are previewable, versioned edit plans that preserve semantics or require explicit review; generated source is updated at its generator origin; concurrent other-agent work is never overwritten. | LSP-03, INTEGRATION-01 |

## Non-functional requirements

| ID | Requirement | Verification |
|---|---|---|
| NFR-PERF-01 | Ordinary builds start no heavy verification process; LSP typing/hover never triggers deep analysis (MODE-01 plus §12.3 gates 1-8 of the design). | MODE-01, benchmark protocol §12.2 |
| NFR-PERF-02 | Primitive-backed units add no per-value tag or heap object; static state markers add no stored field; conversions and boundary checks are measured separately from "zero overhead" claims. | UNIT-10, STATE-03, §12.3 gates 3-5 |
| NFR-PERF-03 | Metadata queries reuse canonical summaries; no per-hover workspace rescan; deep jobs are bounded and cancellable and never block typing. | LSP-01, MODE-01 |
| NFR-SEC-01 | No new hidden panic/trap paths in constructors, transitions, or checked conversion; predicates used for safety are total with bounded permitted effects. | INV-01..INV-03, UNIT-07 |
| NFR-COR-01 | Existing contract, effect, MIR, layout, and edit engines are extended, not duplicated; no third effect taxonomy. | EFF-01..EFF-05 code review |

## Traceability

Every REQ above maps to at least one acceptance test ID from the design §12.1; executable SPipe/SSpec realizations are created in `test/03_system/app/compiler/feature/stronger_types_unified_unit_spec.spl` and unit specs under `test/01_unit/compiler/` during the design/impl steps (see `doc/03_plan/sys_test/stronger_types_unified_unit.md`).
