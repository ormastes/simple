# interpreter BDD omitted structured test evidence
## RESOLVED 2026-11-25 — producer fixed; pure-Simple consumer decoder landed

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

## Verification 2026-11-25 — code fix complete on release/1.0.0

The 2026-11-03 consumer repair candidate has LANDED on release/1.0.0
(a98bed208e2):

- The shared pure-Simple decoder exists as
  `std.nogc_sync_mut.spec.evidence_result.parse_test_result_evidence_v1` and is
  used by BOTH consumers named in the candidate:
  `src/app/test_runner_new/inprocess_probe.spl:40` and
  `src/app/test_runner_new/test_runner_single.spl:823`.
- The decoder spec exists at
  `test/01_unit/app/test_runner_new/structured_result_decoder_spec.spl` and
  covers exactly the cases the candidate lists: the malformed failure count
  (`simple-bdd-v1\n2\nnot_number\n` → rejected, not authenticated as passes),
  valid zero tallies, trailing/missing wire, noncanonical counts, and
  integer/sum overflow.
- The strict wire check also lives in
  `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl:1056-1066`
  (exact `simple-bdd-v1\n{passed}\n{failed}\n` frame match).

Together with the producer fix recorded above (interpreter result paths route
through one recorder emitting `simple-bdd-v1`), the code defect is closed.
Remaining items are release-process, not code: producer binary redeploy /
Stage-4 deployment admission, which requires a qualified self-hosted CLI.

Verification limit: spec execution at this HEAD is blocked by the pinned Rust
seed rejecting `@representation_boundary` (cfd89933699), which fails the test
runner's own load; verified by code inspection of the modules cited above.
