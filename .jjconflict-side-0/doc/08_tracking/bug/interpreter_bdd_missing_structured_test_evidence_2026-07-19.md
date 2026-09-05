# interpreter BDD omitted structured test evidence

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
