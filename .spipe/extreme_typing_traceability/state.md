# Extreme typing and end-to-end traceability

## Task Type

feature — selected capability scope; current delivery is design and planning.

## Refined Goal

Extend the existing traceability roadmap with a compiler-owned robust public
semantic-type contract and shared CLI/LSP/Slop/Caret navigation, evidence,
source, history, and agent-overlay projections.

## Selected policy

On 2026-11-01 the user confirmed that robust/critical/verified public Simple
APIs must not expose raw true builtins, including text, char and bool; public
generics must preserve semantic-domain safety. Easy nominal type creation and
typed literals are required ergonomics, not grounds for primitive exemptions.
Private implementation representation remains allowed. The selected feature
requirements are authoritative; remaining policy/NFR options are not selected.

## Acceptance Criteria

- AC-DOC-1: Reconcile the supplied proposals with release source
  `3273833de3dfe9ea8bc56d0cd877fa05bc1402db`, preserving source-only qualifiers
  and the existing 20 REQ-TRC/40 AC-TRC baseline.
- AC-DOC-2: Record selected extreme-typing constraints, conditional architecture,
  detailed contracts, UI views, phase dependencies, owner boundaries and a
  requirement-to-acceptance plan without claiming executable acceptance.
- AC-DOC-3: Update the guide, feature/layer knowledge routes, historical
  newunit allowlist clarification, and original roadmap through additive links.
- AC-DOC-4: Review scope, local links, fences, layout and diff hygiene; land
  the reviewed documentation through a PR into release/1.0.0.

## Cooperative Review

Astra authored the design; a separate high-effort Astra agent reviews it.
Luna validates bounded documentation structure. Parent owns integration.
Shared implementation interfaces, SSpec step/helper names, and future compile
and test ownership are defined in the agent-task plan. No source implementation
or production execution was performed in this documentation delivery.

## Phase

design-reviewed — source-checked proposal and selected constraints; feature
implementation, runnable SSpec, generated manuals, engine parity, performance,
proofs and qualification remain open. No feature/verify/release PASS is claimed.

## Evidence and scope

The local/domain research, architecture/TLDR, detailed design, UI sketches,
system-test and agent-task plans share the `extreme_typing_traceability` stem.
The knowledge selection receipt is manually derived, not a successful selector
execution. Existing accepted traceability NFRs remain in force; new budgets
remain pending selection and measurement.

No operational skill instructions or generated manuals were changed to
advertise unimplemented commands. New runtime bug repairs are outside this
documentation pass; observed source gaps and their owner paths are retained in
the local audit and implementation plan.

The unrelated `.spipe/release_phase3_20261101/state.md` and original checkout's
dirty files are excluded from this change. The Phase 3 producer availability
blocker does not prevent reviewing documents, but it still prevents executable
compiler/test qualification on this host.

## Documentation validation

Astra's independent high-effort draft review found zero P0/P1 issues. Luna's
bounded pass confirmed relative Markdown links, fence balance and zero
executable SSpec files under doc/06_spec. The identified extra EOF blank line
was corrected; staged diff whitespace and working/staged direct-env-runtime
guards passed. These are documentation checks, not feature execution evidence.
Exact-commit review and PR merge are recorded by GitHub delivery provenance.
