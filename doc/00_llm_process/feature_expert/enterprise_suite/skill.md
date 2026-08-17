# Feature Expert: enterprise_suite

## Role

Own process knowledge for the Simple Enterprise Suite: the shared hardened
HTTP core, the durable enterprise store, the guarded-command business
verticals, and the web app in front of them. Lane state:
`.spipe/simple_enterprise_suite/state.md`.

## Module map (current, 2026-08-16)

### Foundation

| Module | Files | What it owns |
|---|---|---|
| `src/lib/common/net/http_core.spl` | 1 | Shared protocol core: parser limits, `body_decision`, bounded chunked decode, `path_is_safe`, route matching. Consumed by **both** `nogc_sync_mut/http_server` and `nogc_async_mut/http_server` — the tier copies of `std.http.{limits,path_security}` are unified onto it. |
| `src/lib/nogc_sync_mut/enterprise_store/store.spl` | 29 fns | Migrations, unit-of-work (`uow_begin`/`uow_rollback`), idempotency, outbox rows, tenant filtering, `store_backend_acid` honesty probe. |
| `.../enterprise_store/records.spl` | 13 fns | Row helpers + the **period-lock seam**: `period_latest_close`, `journal_post_allowed`, `journal_post_pair`. Sale and restaurant journal posting are thin wrappers, so both inherit the finance lock; dependency direction stays finance -> store. |
| `.../enterprise_store/file_backend.spl` | 11 fns | `SPLSTORE1` file backend used when sqlite is unavailable (incl. SimpleOS). Declares its `rt_file_*` externs locally. |
| `.../enterprise_store/audit_hash.spl` | 4 fns | sha256 audit chain (`audit_verify_chain`). |
| **faults seam** | in `store.spl` | `StoreFaults`, `store_faults_none()`, `store_faults_failing_commit()`, threaded through `buffered_commit` — the only supported way to drive commit-failure paths in specs. |

### Business verticals (all guarded-command, all on the frozen `foundation` contracts)

| Module | Files | Notes |
|---|---|---|
| `enterprise_sale/foundation.spl` (6 fns) | frozen contracts | `role_allows`, and the **executable** closed reason set `reason_set()` / `reason_allowed()`. Specs assert set membership by CALLING these, never by grepping prose. |
| `enterprise_sale/goods_sale.spl` (13) | orders, stock ledger, balanced journal |
| `enterprise_booking/booking.spl` (14) | resources, holds, confirm/cancel/no-show, `ranges_overlap` |
| `enterprise_restaurant/restaurant.spl` (15) | table sessions, line transitions, bill close |
| `enterprise_payment/payment.spl` (11) | intents, `provider_verify` boundary |
| `enterprise_hcm/hcm.spl` (18) | hire/terminate, clock in/out, leave request/decide, payroll **input** export |
| `enterprise_procurement/procurement.spl` (16) | requisition -> PO -> receive -> invoice, three-way reconcile |
| `enterprise_finance/finance.spl` (10) + `finance_async.spl` | trial balance, AR, AP, insert-only period close |
| `enterprise_outbox/outbox_worker.spl` (11) | drain/dispatch + reconciliation |
| `enterprise_channel/channel_hub.spl` (25) | external marketplace adapters, inbox dedup, checkpoints |
| `enterprise_session/{session,throttle}.spl` (9+4) | session issue/verify + login throttling |

### Web app — `src/app/enterprise_store_app/`

`main.spl` (router) + `web_common.spl` (hardened prelude: `esc()`, `deny()`
with an explicit arm for **every** closed-set reason) + route families:

- `auth_routes.spl` — `/auth/login`, `/auth/logout`
- storefront (in `main.spl`) — `/store/catalog`, `/store/order`, `/store/pay`, `/store/order/:id/receipt`
- `booking_routes.spl` — `/booking/`, `/booking/resources`, `/booking/hold|confirm|cancel`, `/booking/:id/status`
- `restaurant_routes.spl` — `/restaurant/`, `/restaurant/table/open`, `/restaurant/order/line`, `/restaurant/kitchen/ready`, `/restaurant/line/served`, `/restaurant/bill/close`, `/restaurant/session/:table/view`
- `hcm_routes.spl` — `/hcm/`, `/hcm/employees`, `/hcm/hire`, `/hcm/clock/in|out`, `/hcm/leave/request|decide`, `/hcm/payroll/export`
- `procurement_routes.spl` — `/proc/`, `/proc/pos`, `/proc/requisition[/approve]`, `/proc/po`, `/proc/receive`, `/proc/invoice`, `/proc/reconcile`
- `finance_routes.spl` — `/fin/`, `/fin/trial-balance`, `/fin/ar`, `/fin/ap`, `/fin/period/close|status`
- `dashboard.spl` — `/admin/dashboard` roll-up, degrading to 0/empty via `store_migration_applied` when a vertical's schema is absent

### Conformance gate

`test/01_unit/lib/nogc_sync_mut/enterprise_conformance_spec.spl` drives REAL
commands across all verticals and asserts the guarded-command invariants
(replay-before-feasibility, closed reason set). No source-text assertions.
Contract doc: `doc/07_guide/app/enterprise/guarded_command_contract.md`.

`test/01_unit/lib/nogc_sync_mut/enterprise_interface_conformance_spec.spl`
(W19-C) is the narrower sibling: it fences the two INTERFACE invariants of the
contract layer independently of any vertical's flow — (1) the closed reason set,
with a **reproduce-first bite** (`reason_allowed` must reject
`__spec_bogus_reason__` and case/underscore variants; widen the set and it goes
red) plus a live denial swept out of every vertical; (2) the **cross-OS SHA-256
facade** `audit_sha256_hex` pinned digest-identical to the canonical vectors AND
to `std.common.crypto.sha256.sha256_text`, then the store's facade-hashed audit
chain verified end to end.

### Interface coherence matrix (W19-C audit, HEAD 2026-08-17)

Every vertical audited against three invariants: (A) denies only with
`reason_set()` members, (B) runs `session -> rbac -> validation -> idempotency ->
effects`, (C) routes hashing through `audit_sha256_hex`, not
`std.common.crypto.sha256` directly. Full matrix + method:
`doc/07_guide/app/enterprise/README.md` (the suite index page).

- **A and B: PASS for all 10 verticals.** Every `denied(...)` / direct
  `CommandResult(...)` reason is in the closed set; guard rungs are line-ordered
  correctly everywhere.
- **C: one VIOLATION — W19-C-1.**
  `enterprise_payment/payment.spl:59,78` imports and calls `sha256_text`
  directly in `provider_sign`/`provider_verify`, bypassing the facade — so the
  payment vertical will not build standalone-SMF (SimpleOS). Audit chain is
  unaffected (payment's audit rows still route via the store facade). **Owner:
  payment lane**, not W19-C. Fix: swap the import to `audit_sha256_hex` (proven
  digest-preserving by the interface spec). Store + session vertical comply.
- **Landing in parallel (absent at this HEAD): CRM, fulfillment.** When they
  land, add matrix rows + a conformance-sweep entry and re-audit invariant C.

## Verification commands

Run **one spec per process** (`SIMPLE_TIMEOUT_SECONDS=900`), read the
`SPEC FILE VERDICT` line, and record the binary identity once
(`readlink -f bin/simple` + `bin/simple --version | head -1`).
A ready-made driver lives at `build/w10a/run.sh` in the W10-A worktree (writes
one ANSI-stripped log per spec under `build/w10a/logs/` and one verdict line
per spec into `build/w10a/verdicts.txt`).

**Current whole-suite number (2026-08-17, lane W13-B, tip = detached main
`bdafd9d5b5a` — this supersedes the 49/49 W10-A sweep, which ran a
SELF-SELECTED 49-file subset that still omitted most of the `http_server`
tier):**
**71/71 canonical spec files GREEN, 635 examples executed, 635 passed,
0 failed, 0 dropped, 0 timeouts, 0 environment-blocked spec rows** — 29 unit
http_server-tier + 8 unit enterprise + 14 system + 21 ubs_test (llm_caret
tier1_enterprise_transport counted in the enterprise-unit group),
one spec per process. This list is now the COMPLETE on-disk enumeration, not a
curated subset (W13-B folded in the 21+ http_server-tier specs that had never
been swept — the previously-red ones, e.g. `security_headers_spec`,
`rate_limit_spec`, `request_validation_spec`, `range_numeric_guard_spec`,
`security_context_dispatch_spec`, are all GREEN on this tree: the W11-A/W11-B
fixes landed). Binary:
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
(Rust bootstrap seed, 59,536,728 bytes, 2026-08-16 22:59 UTC), interpreter mode.

**This list is AUTHORITATIVE and MUST equal the on-disk enumeration.** Run the
mechanical drift guard before trusting the list — it enumerates from disk and
fails if the count drifts from the recorded 71:

```bash
sh scripts/check/check-enterprise-suite-enumeration.shs   # PASS — 71 spec(s) enumerated, matches EXPECTED (71)
```

The stale `test/unit/**` mirror tree is deliberately EXCLUDED: it holds
divergent duplicate copies of these http_server specs, 5 of which are RED while
their canonical `test/01_unit/**` twins are all GREEN. **These 5 are tracked
and being fixed by lane W16-B — NOT silently green:**

| Mirror spec (test/unit/...) | result | canonical twin | owner |
|---|---|---|---|
| `lib/http_server/csrf_spec.spl` | rc=1, failed=10 | 24/24 GREEN | W16-B (real) |
| `.../http_server/static_file_compression_cache_spec.spl` | rc=1, failed=1 | 7/7 GREEN | W16-B (real) |
| `.../http_server/static_file_handler_compression_spec.spl` | rc=1, failed=3 | 9/9 GREEN | W16-B (real) |
| `.../http_server/compression_spec.spl` | rc=143, NO verdict | 20/20 GREEN | W16-B (harness SIGTERM-under-load; no verdict = not a pass, re-run alone) |
| `.../http_server/static_compression_cache_spec.spl` | rc=143, NO verdict | 8/8 GREEN | W16-B (harness SIGTERM-under-load; re-run alone) |

That divergence is a test-tree-mirror defect fenced by
`check-test-tree-divergence.shs`, NOT an enterprise-suite regression.

The authoritative spec list is:

```bash
# unit — http_server tier (canonical test/01_unit only)
bin/simple test test/01_unit/lib/common/net/http_core_spec.spl
bin/simple test test/01_unit/lib/http_server/accept_header_quality_spec.spl
bin/simple test test/01_unit/lib/http_server/chunked_body_boundary_spec.spl
bin/simple test test/01_unit/lib/http_server/chunked_rejection_spec.spl
bin/simple test test/01_unit/lib/http_server/chunked_size_overflow_spec.spl
bin/simple test test/01_unit/lib/http_server/csrf_spec.spl
bin/simple test test/01_unit/lib/http_server/parser_limits_spec.spl
bin/simple test test/01_unit/lib/http_server/path_safety_spec.spl
bin/simple test test/01_unit/lib/http_server/range_numeric_guard_spec.spl
bin/simple test test/01_unit/lib/http_server/rate_limit_spec.spl
bin/simple test test/01_unit/lib/http_server/request_validation_spec.spl
bin/simple test test/01_unit/lib/http_server/security_context_dispatch_spec.spl
bin/simple test test/01_unit/lib/http_server/security_headers_spec.spl
bin/simple test test/01_unit/lib/http_server/worker_static_file_spec.spl
bin/simple test test/01_unit/lib/nogc_async_mut/http/http_hardening_spec.spl
bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_dynamic_dispatch_spec.spl
bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_parser_limits_spec.spl
bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_path_safety_spec.spl
bin/simple test test/01_unit/lib/nogc_async_mut/http_server/compression_spec.spl
bin/simple test test/01_unit/lib/nogc_async_mut/http_server/phase_result_headers_spec.spl
bin/simple test test/01_unit/lib/nogc_async_mut/http_server/protocol_handler_spec.spl
bin/simple test test/01_unit/lib/nogc_async_mut/http_server/range_numeric_guard_spec.spl
bin/simple test test/01_unit/lib/nogc_async_mut/http_server/static_compression_cache_spec.spl
bin/simple test test/01_unit/lib/nogc_async_mut/http_server/static_file_compression_cache_spec.spl
bin/simple test test/01_unit/lib/nogc_async_mut/http_server/static_file_etag_spec.spl
bin/simple test test/01_unit/lib/nogc_async_mut/http_server/static_file_handler_compression_spec.spl
bin/simple test test/01_unit/lib/nogc_async_mut/http_server/static_file_range_parse_spec.spl
bin/simple test test/01_unit/lib/nogc_sync_mut/http_server/range_numeric_guard_spec.spl
# unit — enterprise store/outbox/channel/conformance (+ llm_caret transport)
bin/simple test test/01_unit/app/llm_caret/messaging/tier1_enterprise_transport_spec.spl
bin/simple test test/01_unit/lib/nogc_sync_mut/enterprise_channel/channel_hub_spec.spl
bin/simple test test/01_unit/lib/nogc_sync_mut/enterprise_conformance_spec.spl
bin/simple test test/01_unit/lib/nogc_sync_mut/enterprise_interface_conformance_spec.spl
bin/simple test test/01_unit/lib/nogc_sync_mut/enterprise_outbox/outbox_worker_spec.spl
bin/simple test test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_audit_hash_parity_spec.spl
bin/simple test test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_file_backend_spec.spl
bin/simple test test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_harden_spec.spl
bin/simple test test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_spec.spl
# system
bin/simple test test/03_system/app/enterprise/back_office_web_spec.spl
bin/simple test test/03_system/app/enterprise/booking_vertical_spec.spl
bin/simple test test/03_system/app/enterprise/enterprise_auth_throttle_spec.spl
bin/simple test test/03_system/app/enterprise/enterprise_security_audit_spec.spl
bin/simple test test/03_system/app/enterprise/enterprise_web_app_spec.spl
bin/simple test test/03_system/app/enterprise/finance_vertical_spec.spl
bin/simple test test/03_system/app/enterprise/goods_sale_vertical_spec.spl
bin/simple test test/03_system/app/enterprise/hcm_vertical_spec.spl
bin/simple test test/03_system/app/enterprise/payment_boundary_spec.spl
bin/simple test test/03_system/app/enterprise/procurement_vertical_spec.spl
bin/simple test test/03_system/app/enterprise/restaurant_vertical_spec.spl
bin/simple test test/03_system/app/enterprise/store_app_spec.spl
bin/simple test test/03_system/app/enterprise/store_web_harden_spec.spl
bin/simple test test/03_system/web/server/http_dynamic_dispatch_live_socket_spec.spl
# ERP example suite (21 specs)
for s in examples/12_business/simple_erp/ubs_test/*_spec.spl; do bin/simple test "$s"; done
```

Standing gates:

```bash
sh scripts/check/check-enterprise-cross-os.shs      # PASS — 8 probe(s), host + x86_64-unknown-simpleos, SMF magic
sh scripts/check/check-c-runtime-compiles-push.shs  # PASS — 102 file(s) compiled, 0 errors (2 external-dep skips)
sh scripts/check/check-sqlite-backend-acid.shs      # BLOCKED (expected) — see below
```

Verbatim gate verdicts on tip `0a12ca93433` (2026-08-17, W10-A):

- `PASS — 8 probe(s) checked, each compiles host + x86_64-unknown-simpleos with SMF magic`
- `PASS — 102 file(s) compiled, 0 errors (2 skipped for unavailable external dependencies)`
- `BLOCKED — AOT native build failed: error: codegen: undefined symbol: rt_sqlite_open`

The ACID gate's BLOCKED message has TWO known shapes. In a lane worktree (this
run) it is the real undefined-symbol error above — the seed's AOT codegen has no
`rt_sqlite_*` symbols to link. The main tree instead blocks earlier on a stale
runtime archive. Either way the gate is environment-blocked, not a red; the
resume path is a stage4 self-hosted native deploy.

Do NOT run the OVMF in-guest gate casually — it is very long and owned by the
SimpleOS lanes.

## Environment-blocked rows (with resume commands)

| Row | Why blocked | Resume |
|---|---|---|
| Store ACID evidence | Interpreter `rt_sqlite` externs are a non-ACID emulation (transactions no-op, constraints unenforced, WHERE-equality ignored, no UPDATE). `store_backend_acid` reports this at open. | Re-run the store specs on a **native** build with real SQLite: `bin/simple test test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_spec.spl` on a stage4 self-hosted deploy. Bug: `doc/08_tracking/bug/interpreter_sqlite_externs_nonacid_emulation_2026-08-14.md` |
| AC-17 in-guest execution of the store | No OVMF boot lane builds a guest image containing `os.userlib.rt_file_facade` or execs an SMF app; cross-compile + guest-owner rows ARE green. Retained transcript `build/os/ent_store_rung_b_attempt_2026-08-16.serial.log` shows in-guest write rc=0, fsize=5, read-back `[MISS]`. | Dump the first 16 bytes the extraction loop actually sees, then re-run the OVMF lane. See `doc/07_guide/lib/database/enterprise_store.md` § Guest-side extern provider. |
| `riscv32` / `i686` / `armv7` cross-compile probes | Toolchain absent (incl. seed `--backend llvm`). | Re-run `sh scripts/check/check-enterprise-cross-os.shs` once those triples have a toolchain. |
| Public TLS / HTTP2 termination | No direct public TLS from Simple servers yet. | Edge-proxy deployment per the assessment §3.2. |
| `/fin/ap` line items | `fin_ap_open` gates on migration id `proc_001_payables`, which nothing applies; procurement books payables into the shared `journal` under `accounts_payable`. The route prints the authoritative journal total so the page is never silently wrong. | Lane W9-A: add a payables projection in procurement, or repoint `fin_ap_open` at the journal. |

## http_server tier folded into the suite (W13-B, 2026-08-17) — RESOLVED

The 21 `*/http_server/*_spec.spl` files that W10-A found unswept are now
**folded into the authoritative list above** and all GREEN on tip
`bdafd9d5b5a`. The W11-A/W11-B fixes landed since W10-A's sweep: the missing
config constructors (`default_security_headers_config`,
`default_rate_limit_config`) now resolve, and the assertion-level reds are
gone. W13-B re-enumerated the whole enterprise+http_server family from disk and
ran all 71 canonical specs one-per-process — 71/71 GREEN, 635/635 examples.
Drift can no longer go unnoticed:
`scripts/check/check-enterprise-suite-enumeration.shs` fails if the on-disk
count leaves 71.

The only remaining reds are in the stale `test/unit/**` MIRROR tree (divergent
duplicates of these http_server specs), not in the canonical `test/01_unit/**`
tree. See the note under "Verification commands" — owner is the test-tree
mirror sync, fenced by `check-test-tree-divergence.shs`.

### Historical record (W10-A first-sweep state, superseded)

W10-A's first enumeration swept the same set and found **12/21 green, 9 RED —
168 examples, 131 passed, 37 failed**, dominated by a missing library API:

| Spec | executed/passed | Cause |
|---|---|---|
| `lib/http_server/security_headers_spec` | 7/0 | `semantic: function default_security_headers_config not found` |
| `lib/http_server/rate_limit_spec` | 6/0 | `semantic: function default_rate_limit_config not found` |
| `lib/http_server/request_validation_spec` | 11/0 | same class — missing config constructor |
| `lib/http_server/range_numeric_guard_spec` | 1/0 | assertion: `expected subject to be truthy, got false` |
| `lib/http_server/security_context_dispatch_spec` | 6/5 | 1 assertion |
| `lib/nogc_async_mut/http_server/compression_spec` | 19/11 | 8 assertions (`expected gzip to equal lz4`) |
| `lib/nogc_async_mut/http_server/protocol_handler_spec` | 8/7 | 1 assertion |
| `lib/nogc_async_mut/http_server/range_numeric_guard_spec` | 1/0 | assertion |
| `lib/nogc_async_mut/http_server/static_compression_cache_spec` | 8/7 | 1 assertion |

`/usr/bin/grep -rn 'default_security_headers_config\|default_rate_limit_config' src/`
returns **zero hits** — those functions exist nowhere in the tree, so the three
worst specs are orphaned against an API that was never implemented (or was
removed). Deliberately NOT fixed by W10-A: out of the enterprise lane's scope
and not caused by this round's merges. Needs an owner.

## Landmines (each of these has already cost a lane real time)

1. **Interpreter sqlite is non-ACID.** Any durability/constraint/UPDATE claim
   proven only on the interpreter is vacuous. Design around it: insert-only
   tables, pure-Simple tenant filtering, prepared binds.
2. **sqlite caches per db path in-process** — two scenarios sharing a path
   share state. **One db path per scenario**, always.
3. **Outbox naming collision** — `std.enterprise_outbox` (the worker) vs the
   store's own `outbox` rows; and the sync-tier impl vs the `nogc_async_mut`
   wrapper of the same name. Import the exact tier you mean.
4. **Seed `spipe-docgen` subcommand drops argv.** Use
   `bin/simple run src/app/spipe_docgen/spipe_docgen/main.spl <spec> ...`
   instead. Bug: `doc/08_tracking/bug/spipe_docgen_subcommand_argv_drop_2026-08-16.md`.
   (The app carries a `/proc/self/cmdline` argv-recovery fallback on Linux.)
5. **NEW, cost lane W4-A days: a `.spl`-declared `extern` can bind to a C
   runtime stub instead of the Simple module that `@export("C")`s the same
   name.** `file_backend.spl` and `os/userlib/rt_file_facade.spl` both declare
   `rt_file_*` locally; if a same-named stub exists in `src/runtime`, the link
   silently prefers it and every call "succeeds" while doing nothing
   observable (rc=0, plausible fsize, empty read-back). Symptoms look like a
   storage bug, not a linking bug. **Before debugging store durability,
   confirm which definition is actually bound.** Two real defects hid behind
   this: the Simple->C `text` ABI is ONE `RuntimeString` pointer (not
   ptr+len — the wrong-length write masqueraded as disk-full), and a FAT32
   per-call aligned-buffer leak.
6. **Never share `build/` across worktrees.** Cross-worktree compile-cache
   contamination made red-first evidence unreliable for several lanes (a
   sabotaged module still resolved from another worktree's cache). Verify
   `stat -c %F build` prints `directory`, not `symbolic link`, before
   producing any red-first evidence. The vacuity audit that discharged this
   debt is in `guarded_command_contract.md` § Vacuity audit.
7. **Replay before state-dependent feasibility.** The suite's one systemic
   defect class: 14 commands across 6 modules evaluated feasibility before
   replay detection, so replaying a command that consumed its own precondition
   returned the wrong reason. Rule doc:
   `doc/07_guide/app/enterprise/replay_and_state_dependent_validation.md`.
   Corollary from the period-lock merge: a replay must return its recorded
   result **before** the period check — a replay posts nothing.
8. **`uow_rollback` does not undo issued inserts on this backend.** Validate
   BEFORE `uow_begin`, never inside the UoW.
9. **`reason=daemon-no-response budget_ms=120000` is harness plumbing, not a
   regression.** It shows up as `declared>=1 executed=1 passed=0 failed=1
   timeout=1` — note the `declared>=1`, far below the spec's real example
   count, which is the tell. Observed on `ubs_test/restaurant_lane_spec.spl`
   during the 2026-08-16 sweep; a plain standalone re-run gave 12/12. Always
   re-run a red once standalone before diagnosing the code. (It did NOT recur
   in the 2026-08-17 W10-A sweep — `declared>=12 executed=12 passed=12` — which
   confirms it is load/timing-dependent plumbing, not the spec.)
10. **Never trust the recorded spec list as the enumeration.** The 48/49-file
    lists in this doc silently omitted 21+ `http_server` tier specs. W13-B
    folded the complete on-disk set in (now 71 canonical) and added a mechanical
    guard, `scripts/check/check-enterprise-suite-enumeration.shs`, that FAILS if
    the on-disk enumeration drifts from 71. Run it every sweep BEFORE trusting
    the list; a spec that appeared or vanished trips the guard and is itself a
    finding. When you legitimately add/remove a suite spec, update the wiki list
    AND the `EXPECTED=71` in that script together.
11. **The `test/unit/**` mirror tree is stale and diverges from `test/01_unit/**`.**
    6 http_server mirror copies are RED while their canonical twins are GREEN.
    Sweep only the canonical `test/01_unit/**` tree; the mirror is fenced by
    `check-test-tree-divergence.shs` and is not the enterprise suite's problem.

## Guides

- `doc/07_guide/lib/database/enterprise_store.md` (surface, backend honesty,
  failure-path hardening, cross-OS matrix, file backend, outbox worker)
- `doc/07_guide/app/enterprise/` — `store_app.md` (all route families incl.
  back-office + auth/throttle), `guarded_command_contract.md`,
  `replay_and_state_dependent_validation.md`, `booking.md`, `restaurant.md`,
  `payment.md`, `hcm.md`, `procurement.md`, `finance.md`, `channel_hub.md`
- `doc/07_guide/lib/networking/http_server_hardening.md`
- Assessment: `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`
