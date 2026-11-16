# TODO: more than one AGENT per Linux service incarnation

Status: open (filed with milestone_0021 PR2, 2026-11-16).

milestone_0021 lets the V4 installed Linux service run exactly ONE agent at a time
per service incarnation: the agent borrows the service's single fresh-epoch
admission through the workspace-root loan (R3) and the service loan (R2), and a
second lend is refused (`...-workspace-root-loan-active`). Running several agents
concurrently in one incarnation needs per-agent loans (or a loan table) and a
capacity owner that settles more than one associated execution. Out of scope for
milestone_0021.

Design: `.spipe/simple_orchestrator/continuation_20261116/milestone_0021_agent_owner_v4/DESIGN.md`
