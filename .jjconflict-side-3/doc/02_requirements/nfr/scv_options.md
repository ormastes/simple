# SCV NFR Options

Status: option record, 2026-05-14.

## Option A: Correctness And Durability First

Description: Optimize first for byte-exact preservation, atomic metadata updates, recoverable operation history, and portable Simple implementation.

Pros:

- Matches VCS safety expectations.
- Makes parser/merge failures non-destructive.
- Works across x86-64, ARM64, and compatibility targets including RISC-V.

Cons:

- Some advanced diff/pack performance is deferred.

Effort: high.

Decision: selected by user direction.

## Option B: Structural Intelligence First

Description: Prioritize Tree-sitter, GumTree-style matching, and semantic diff before raw storage completeness.

Pros:

- Produces differentiated demos earlier.

Cons:

- Higher data-loss risk when parser support is incomplete.
- Violates the byte-exact foundation requirement.

Effort: high.

Decision: rejected.

## Option C: Performance First

Description: Prioritize pack files, FastCDC, and compression before operation-log and private savepoint completeness.

Pros:

- Better large-file storage earlier.

Cons:

- Harder to validate correctness and recovery semantics.
- Premature before object identity and reachability are stable.

Effort: high.

Decision: rejected for MVP start.
