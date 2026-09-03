# MDSOC++ Real Product-Generation Upgrade Report

## Scope

The existing IDE/tooling large-program pilot now has a real mutable generation
owner rather than only a candidate-admission receipt. The implementation does
not modify the KPF ABI generator or VS Code files.

## Implemented

- deterministic document-state migration before publication;
- one-owner atomic active/draining deployment swap;
- old-generation retention with explicit inflight drain accounting;
- rollback to the exact retained deployment and state;
- retirement that permanently closes the rollback window;
- bounded retained transition receipts with fail-closed capacity admission;
- typed failures for rejected upgrades, invalid drains, overlapping upgrades,
  unavailable rollback, and receipt exhaustion.

## Mutation-Sensitive Evidence

The executable system spec verifies exact generation, schema, state, sequence,
phase, inflight, and receipt-count values. It removes the required migration
declaration and proves the candidate is not published. It also over-counts a
drain, exhausts receipt capacity, and attempts rollback after retirement; each
mutation must leave the authoritative generation unchanged.

## Architecture

Atomicity derives from one non-yielding mutable owner operation. Candidate seal
and migration complete before the active pair changes. The old deployment and
state remain an inseparable rollback snapshot until their inflight count reaches
zero. Receipts are evidence only and grant no authority.

## Verification

Executed with the admitted pure-Simple runtime at
`/Users/ormastes/simple/bin/release/macos-arm64/simple`:

- generation-upgrade system spec: 4/4 PASS;
- existing IDE/tooling pilot: 8/8 PASS;
- MDSOC++ sealer unit spec: 5/5 PASS;
- MCP stdio integration smoke: 1/1 PASS;
- diff/stub/spec-layout hygiene: PASS.

The required broad `check` commands for `src/compiler`, `src/lib`,
`src/app/mcp`, and `src/app/simple_lsp_mcp` reached the admitted runtime's
existing lint/format subprocess failure (`exit -1`) and exited 255 without a
source diagnostic. They are not claimed as passing. KPF ABI generator and VS
Code paths were excluded by lane ownership.
