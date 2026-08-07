# `lab_server.spl` doesn't cap oversized individual HTTP header lines

**Found:** 2026-08-07, during H3 robustness evidence
(`test/03_system/tools/simple_lab/lab_robustness_spec.spl`, fuzz-lite corpus).

## Symptom

A `GET /api/lab/status` request carrying one legitimately-authenticated header
plus a single 20,000-byte header line (`X-Fuzz-Oversized: xxxx...`, well over
an intended 8,192-byte cap) is accepted and answered normally with `200`,
instead of being rejected with a `4xx`. Reproduced via a real loopback socket
against a real `lab_server.spl` subprocess, not a mock.

## Impact

Not a crash/panic — the server handled the oversized header without
misbehaving, so this is a bounds-enforcement gap, not a robustness/stability
bug. But H1's stated bounds contract (design §8.2, and this spec's own
in-repo comment referencing "well over the 8192-byte cap") implies an
enforced per-header-line size limit that `lab_hardening.spl` does not
currently check. All 8 other fuzz-lite cases (6 malformed-JSON-body variants,
a 110-header request, and a truncated WebSocket handshake mid-write) DID get
the expected `4xx`/clean-close treatment — this is the one gap.

## Unblock condition

Add a per-header-line length check to `lab_hardening.spl`'s request parsing
(alongside the existing body-size-413 and too-many-headers checks, which both
already work correctly per this same fuzz run) and return `4xx` when a header
line exceeds the intended cap.

## Status

Open — left the assertion RED in
`test/03_system/tools/simple_lab/lab_robustness_spec.spl` rather than
weakened, per `.claude/rules/testing.md`. Real evidence still recorded for
the two examples that DID fully pass: load smoke (200/200 authenticated
`GET /api/lab/status`, zero non-200, panic-free) and the 100-cell soak (one
real session, 100/100 sequential real cell executions via
`.../cells/:cid/execute`, all `ok:true`, panic-free, session count correct
afterward). See `doc/09_report/notebook_lanes_robustness_evidence_2026-08-07.md`.
