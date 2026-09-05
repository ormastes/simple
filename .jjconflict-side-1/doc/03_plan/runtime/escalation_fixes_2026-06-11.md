# Escalation Fixes 1–7 — Execution Plan (2026-06-11)

User approved GO on all 7 escalations from
`doc/03_plan/runtime/hardening_formal_verification_2026-06-11.md` (FINAL STATUS).
Execution: parallel Sonnet agents, disjoint scopes, Fable review + commit per
batch with pull-rebase-push sync. Every fix ships a regression spec; Lean models
that pinned the OLD behavior are updated in the same batch.

## E1 — AOP runtime `Around` proceed (F1)  [agent A1, aop.spl]

Design (Option A, adapted to Simple constraints — no `Any`, read-only nested
closure capture, fn-fields exported statement-form):

- New class `ProceedCell` in aop.spl: fields `called: i64`, `ok: bool`,
  `error: text`; `me mark_called()`, `me set_ok()`, `me set_err(e)`. Object
  fields are mutable through me-methods even when captured read-only.
- `Advice` gains optional around contract WITHOUT generics: the around handler
  type is `fn(AdviceContext, fn() -> Result<(), text>) -> Result<(), text>`.
  The proceed thunk is built INSIDE generic `wrap<T>` closing over `func` and a
  local result slot object (`ResultSlot<T>`-shaped class local to wrap's module
  with `me set(v: T)` — wrap<T> instantiates it, so no erasure needed: the
  thunk signature stays `fn() -> Result<(), text>` while the value lands in the
  slot object).
- Semantics: Around with handler: handler runs; calling proceed() executes the
  target exactly once and fills the slot. proceed called 0 times → wrap returns
  Err("around advice did not call proceed") + denial recorded. proceed called
  >1 → second call returns Err immediately (cell.called guard), recorded.
  Handler Err → wrap Err + denial (target may or may not have run — recorded
  which, via cell.called).
- Backward compat: existing `Advice(kind: Around, handler: pre-hook)` registrations
  keep pre-hook behavior; the proceed contract applies to advices registered
  through a new `Advice.around(name, around_handler)` constructor (additive).
- Spec: proceed-once runs target & returns value; no-proceed denies; double
  proceed errs; pre-hook compat preserved.

## E2 — After-denial masking (F3)  [agent A1, same file]

After advice Err keeps returning Err (enforcement preserved) but the denial
record is explicit that the target executed: message prefix
`after(target-executed)`. Spec pins the marker.

## E3 — Transitive capability revoke (kernel F1)  [agent A2]

`os/kernel/ipc/capability.spl` (+ types): add provenance to grants
(token id + parent token id chain). `cap_revoke` becomes transitive: revoking a
token also revokes every grant derived from it (walk children). Owner-level
`revoke()` stays for direct use. Spec: grant → delegate to other principal →
revoke root → delegate's check fails.

## E4 — Delegation depth enforcement (kernel F2)  [agent A2, same files]

`CapabilityToken` gains `depth: i64` (remaining delegation budget). `derive`/
delegation decrements; at 0, further delegation is refused (deny, not clamp).
Default depth for fresh grants: 2 (matches the documented max-depth-2 rule in
webapp_security guide). Lean model `kernel_capabilities` updated: T2 proves
against the real depth field now; T3 strengthened to transitive revocation.

## E5 — Pager WAL-before-data (db FINDING-T4)  [agent A3]

`dbfs_engine/pager.spl`: pages carry `page_lsn`; `write_page` takes the page's
mutation LSN and refuses (Err) when `wal_flushed_lsn < page_lsn`. WAL exposes
`flushed_lsn()`. Raw pager use without WAL passes `page_lsn = 0` → check
skipped (compat). txn.spl write path threads real LSNs. Lean `db_storage` T4
updated from protocol-level to pager-level statement. Spec: write with
unflushed LSN → Err; after wal flush → Ok.

## E6 — Cooperative green_spawn deferral (B6)  [agent A4]

`concurrent/green_thread.spl` (+ green scheduler glue): green_spawn stops
executing the closure eagerly; it stores the thunk in the task record and the
scheduler executes it on `run_until_idle`/poll. Errors inside a deferred task
must not propagate to the spawner (record per-task death reason, consistent
with W2-5). Known risk: interpreter limitation on closure-in-struct-field —
investigate first; if it blocks, implement the documented fallback (thunk
table keyed by task id at module level) and note it. Spec: spawn does NOT run
body immediately (observe side-effect ordering); run executes all; error task
doesn't kill siblings. Update actor_channel Lean model only if channel/actor
semantics change (they should not).

## E7 — PhaseResult response headers (ESCALATE 10, Option A)  [agent A5]

`nogc_async_mut/http_server`: `PhaseResult.Respond(i64, text, text)` →
`Respond(i64, text, [(text,text)], text)` = (status, reason, headers, body).
Update worker.spl emission (~line 640) to write real header lines, every
`Respond(...)` constructor across http_server (grep all), and fix
`cors_handler` (cors.spl) to put CORS headers (incl. Vary: Origin) into the
header slot instead of the body. Specs: constructor shape + cors_handler emits
headers-not-body (string-level assertion on worker serialization if testable).

## Parallelization

| Agent | Scope (disjoint) | Items |
|-------|------------------|-------|
| A1 | src/lib/nogc_sync_mut/src/aop.spl + aop specs | E1, E2 |
| A2 | os/kernel/ipc/capability*.spl + src/verification/kernel_capabilities + spec | E3, E4 |
| A3 | lib dbfs_engine pager/wal/txn + src/verification/db_storage + spec | E5 |
| A4 | concurrent/green_thread.spl + green scheduler + spec | E6 |
| A5 | nogc_async_mut/http_server (types, worker, phases) + specs | E7 |
| Fable | review, commit/push per batch with sync cycle, fix-forward | all |

## FINAL STATUS — 2026-06-11 (all 7 fixed and pushed)

| Esc | Commit | Verification |
|-----|--------|--------------|
| E1 AOP real Around proceed | 4f1b29dad9 | aop_around_proceed_spec 5/5 |
| E2 after(target-executed) marker | 4f1b29dad9 | aop_denial_visibility_spec 7/7 |
| E3 transitive capability revoke (+syscall 49) | cd745b3c21 | capability_revoke_depth_spec 9/9, ipc_grants 21/21, Lean T3 transitive zero-sorry |
| E4 delegation depth (default 2, deny at 0) | cd745b3c21 | same spec; Lean T1 reproved with depth guard |
| E5 pager WAL-before-data gate | 39fe524041 | pager_wal_gate_spec 13/13, dbfs_engine_pager 8/8, Lean T4 pager-level zero-sorry |
| E6 cooperative green_spawn deferral (B6) | fbaea14ff4 | green_spawn_deferred_spec 5/5 + 5 existing green specs green incl. upstream yield-gap |
| E7 PhaseResult headers + CRLF guard | 8eb08c54f3 | phase_result_headers_spec 16/16 |

Notes recorded during verification:
- Lint SPIPE006/007 steer specs toward bare `expect()` / `expect_not()`; bare
  `expect(cond)` is still a hollow no-op (verified 2026-06-11) while
  `expect_not`/`assert_true` are honest — specs here use `assert_true`.
- New pre-existing bug recorded (not E5's): reserved keyword `gen` as field
  name in dbfs checkpoint structs — doc/08_tracking/bug/
  dbfs_checkpoint_gen_reserved_keyword_2026-06-11.md.
- E6 death-reason fields are plumbing: pure Simple has no try/catch, so
  per-task error capture activates only once a runtime catch hook exists.
- E4 syscall 49 gate is stricter than the plan minimum (SystemPrivilege
  required for transitive revoke) — deny-by-default kept.
