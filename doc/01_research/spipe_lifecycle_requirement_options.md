# SPipe lifecycle requirement options

Status: awaiting user selection. Full destination: the [supplied lifecycle proposal](../04_architecture/spipe_complete_lifecycle.md). These options choose delivery order, not a smaller definition of completion.

Landing note (2026-11-07): the user authorized landing these design and research documents on Simple's `release/1.0.0`. That authorization does not select an implementation option or claim that the proposed lifecycle is implemented.

## Feature options

### A — inventory first, then complete M0–M6 (recommended)

Build the bounded read-only lifecycle doctor and canonical inventory first, then schemas/trace core, state machine and receipts, adapters, incidents, learning and graduated enforcement. Preserve existing BDD commands and reuse existing validators and scheduling.

Pros: establishes current contracts before migration; exposes conflicting/generated guidance; reduces duplicate implementations. Cons: orchestration becomes visible after inventory work. Effort: small-to-medium for inventory/doctor; large multi-stage effort for the complete proposal.

### B — trace/state core first, then complete M0–M6

Start with versioned schemas, lifecycle transitions and gate/evidence semantics, inventorying dependencies during design; complete the doctor and remaining roadmap afterward.

Pros: demonstrates the core workflow earlier. Cons: greater migration/rework risk while existing phase contracts remain incompletely inventoried. Effort: medium-to-large initial core; large multi-stage effort overall.

## NFR options

### 1 — measure first, then enforce observed budgets (recommended)

Record wall time, files/bytes read, output size and peak memory on pinned realistic fixtures. Derive numeric blocking thresholds from those baselines before enforcement. Bound traversal, avoid external/private scope discovery, keep SDN default and JSON explicit, and test missing tools and invalid evidence fail closed.

Pros: consistent with proposal criterion 10; avoids invented performance targets. Cons: requires baseline fixtures before strict performance gates. Effort: medium, alongside each capability.

### 2 — measurements plus owner-selected limits before implementation

Gather the same baselines, then require the owner to choose hard startup/memory/token thresholds before implementing runtime capabilities.

Pros: explicit resource commitments early. Cons: delays implementation and may require revisiting limits as incident/evaluation features arrive. Effort: medium plus owner review.

## Acceptance shared by all selections

Preserve all proposal sections and acceptance criteria as the destination. Never claim roadmap completion from a doctor-only result. Require real positive/negative fixtures, exact revision evidence, authorization before knowledge discovery, compatible provider adapters and independently reviewed PR integration. Release tags/publication remain separately authorized. Stop conditions and bounded verification apply throughout.
