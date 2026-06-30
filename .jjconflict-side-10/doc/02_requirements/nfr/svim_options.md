# svim NFR Options

## Option A — Core Reuse And Stable RPC First

- Pros: enforces one editing engine across shells, keeps automation/test surfaces stable, and aligns with repo RPC patterns.
- Cons: requires explicit portability boundaries up front.
- Effort: medium.

## Option B — UI Fidelity First

- Pros: prioritizes shell polish and richer presentation early.
- Cons: risks shell-specific behavior and duplicated editor logic.
- Effort: medium-high.

## Option C — Parser/Language Services First

- Pros: maximizes syntax and diagnostics depth early.
- Cons: slows down basic editor bring-up and leaves shell/core integration ambiguous.
- Effort: high.

## Selected

Option A is selected by the supplied implementation plan.
