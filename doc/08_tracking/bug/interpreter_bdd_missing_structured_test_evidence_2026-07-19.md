# interpreter BDD omitted structured test evidence
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** PRODUCER FIXED / PURE-SIMPLE CONSUMER DEPLOYMENT PENDING
**Severity:** P1 — `--assert-ran` could not authenticate interpreter results

## Root cause

Interpreter dispatch handles `describe`/`it` before the Simple `std.spec`
implementation, so the Simple evidence writer never runs. Pass/fail/skip
outcomes existed only in Rust's thread-local `BDD_TEST_RESULTS` snapshot.

## Solution

The three interpreter result paths now route through one recorder. When
`SIMPLE_TEST_RESULT_FILE` is set, it serializes the authoritative snapshot as
`simple-bdd-v1`, counting non-skipped passes and failures. Write failure remains
best-effort because the parent consumer rejects absent or malformed evidence.

## Evidence

The focused Rust regression seeds pass, fail, and skipped outcomes and requires
the exact payload `simple-bdd-v1\n1\n1\n`: PASS.

The pure-Simple environment bridge and fail-closed consumer still require an
admitted Stage 4 integration run.


## 2026-11-03 pure-Simple consumer repair candidate

Current release source already includes the evidence-path environment/explicit
transport, local authoritative writer tallies, and a fail-closed `--assert-ran`
consumer in the single runner. Historical producer deployment remains unqualified
on this Windows host. Inspection found a separate concrete consumer gap:
`test_runner_new/inprocess_probe.spl` converted invalid count fields to zero and
ignored trailing lines. For example `simple-bdd-v1\n2\nnot_number\n` could be
accepted as two passes and no failures.

The candidate shares one lightweight pure decoder between the single runner and
the in-process probe. It requires the exact existing versioned wire, canonical
nonnegative integers and a nonoverflowing executed total. It never fabricates
execution for valid zero counts; both consumers retain positive-total admission.
The decoder spec covers passing/failing/zero receipts, the exact malformed failure
count, trailing/missing wire, negative/noncanonical counts and integer/sum overflow.

Status: TEST_BLOCKED. No qualified self-hosted full CLI is installed; no behavioral
spec, compiler/core/lib check, MCP smoke or producer deployment admission was run.
Source/whitespace guards cannot qualify interpreter execution or close this bug.
