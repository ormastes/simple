# Feature Expert: enterprise_suite

## Role

Own process knowledge for the Simple Enterprise Suite: the shared hardened
HTTP core, the durable enterprise store, the guarded-command business
verticals, and the web app in front of them. Lane state:
`.spipe/simple_enterprise_suite/state.md`.

## DB target clarification (2026-08-20)

Simple has **three DB implementations** (canonical map:
`doc/07_guide/lib/database/db_implementations_map.md`): the **textual DB**
(SDN-file store, `SdnDatabase`), the **embedded DB** (SQLite-like in-process
store: `database/pure_sql`, `SdnDatabase`, interpreter `rt_sqlite` emulation)
and the **DB server** (`std.database.server` =
`src/lib/nogc_sync_mut/database/server/` — sessions, deny-wins capabilities,
transactions, commit-before-ack durability, framed transport).
`postgres_mimic` is only a PostgreSQL compatibility surface, not the server.
Enterprise-suite production hardening targets the **DB server** tier; the
embedded DB stays for local/dev/test and as the server's store port.
Hardening landed 2026-08-20: `store_rows` now orders by `id` (deterministic
reads for audit-chain + last-row-wins consumers), and procurement journal
posting routes through `journal_post_pair`/`journal_post_allowed` (closed-period
denial; spec `test/03_system/app/enterprise/procurement_period_seam_spec.spl`).
Master plan:
`doc/01_research/app/office/office_enterprise_suite_audit_architecture_parallel_plan_2026-08-20.md`.

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

## Verification commands

Run **one spec per process** (`SIMPLE_TIMEOUT_SECONDS=900`), read the
`SPEC FILE VERDICT` line, and record the binary identity once
(`readlink -f bin/simple` + `bin/simple --version | head -1`).
A ready-made driver lives at `build/w10a/run.sh` in the W10-A worktree (writes
one ANSI-stripped log per spec under `build/w10a/logs/` and one verdict line
per spec into `build/w10a/verdicts.txt`).

**Current whole-suite number (2026-08-17, lane W10-A, tip `0a12ca93433` — this
supersedes the stale 48/48 429-example sweep, which ran on a tree predating the
AP fix, native-ACID docs and security merges):**
**49/49 spec files GREEN, 439 examples executed, 439 passed, 0 failed,
0 dropped, 0 timeouts, 0 environment-blocked spec rows** — 14 unit + 14 system
+ 21 ubs_test, ~33 min wall total, one spec per process. The set grew from 48
to 49 because `test/03_system/app/enterprise/enterprise_security_audit_spec.spl`
(8 examples) landed since. No harness-plumbing red this time:
`ubs_test/restaurant_lane_spec` reported `declared>=12 executed=12 passed=12`.
Binary: `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
(Rust bootstrap seed, 59,536,728 bytes, 2026-08-16 22:59 UTC).

The spec list is:

```bash
# unit
bin/simple test test/01_unit/lib/common/net/http_core_spec.spl
# http_server tier — DISCOVERY-BASED, do not hand-list (lane W14-C, 2026-08-17).
# The suite IS the glob: any new */http_server/*_spec.spl file is in the suite
# the moment it lands. `test/unit/**` is the legacy mirror and is excluded.
# Enforced by scripts/check/check-http-server-suite-enumeration.shs.
#
# DO NOT re-add hand-listed http_server lines here. The same six
# (async_parser_limits, async_path_safety, async_dynamic_dispatch,
# chunked_rejection, parser_limits, path_safety) have now been resurrected
# THREE times by 3-way merges — the third time (2026-08-21) sitting directly
# above this very comment. Every one is already matched by the glob, so listing
# them runs those specs TWICE per sweep and re-opens the drift hole the loop
# exists to close. The glob is the list.
#
# Deleting them a fourth time is not the fix, and the note you are reading was
# not enough either. As of 2026-08-21 the gate DETECTS the condition: a doc
# carrying the loop AND a live `bin/simple test <http_server spec>` line now
# FAILs, naming each redundant path (selftest fixture 5). Commented paths — like
# the ones in this very note — are excluded, so the warning cannot trip its own
# gate (fixture 6). If a merge brings them back, the gate says so.
#
# This SUPERSEDES the 49/49-green count above for the http_server tier. Current
# sweep, measured one-per-process in a CLEAN WORKTREE at origin/main (not the
# shared checkout — it is chronically stale and produces false reds), Jul-25
# aarch64 binary: 25/27 files green, 290 examples, 275 passed, 15 failed.
# The 2 reds are chunked_body_boundary (7/14) and chunked_size_overflow (4/12),
# both the pre-existing `common_index_of` aliased-import defect noted at
# src/lib/nogc_async_mut/http_server/parser.spl:29 — not enterprise-lane code.
# Evidence: doc/09_report/verify/http_server_suite_enumeration_2026-08-17.md
for s in $(find test -path '*http_server*' -name '*_spec.spl' -not -path 'test/unit/*' | sort); do bin/simple test "$s"; done
bin/simple test test/01_unit/lib/nogc_async_mut/http/http_hardening_spec.spl
bin/simple test test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_spec.spl
bin/simple test test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_harden_spec.spl
bin/simple test test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_file_backend_spec.spl
bin/simple test test/01_unit/lib/nogc_sync_mut/enterprise_outbox/outbox_worker_spec.spl
bin/simple test test/01_unit/lib/nogc_sync_mut/enterprise_channel/channel_hub_spec.spl
bin/simple test test/01_unit/lib/nogc_sync_mut/enterprise_conformance_spec.spl
# system
bin/simple test test/03_system/app/enterprise/goods_sale_vertical_spec.spl
bin/simple test test/03_system/app/enterprise/booking_vertical_spec.spl
bin/simple test test/03_system/app/enterprise/restaurant_vertical_spec.spl
bin/simple test test/03_system/app/enterprise/hcm_vertical_spec.spl
bin/simple test test/03_system/app/enterprise/procurement_vertical_spec.spl
bin/simple test test/03_system/app/enterprise/finance_vertical_spec.spl
bin/simple test test/03_system/app/enterprise/payment_boundary_spec.spl
bin/simple test test/03_system/app/enterprise/store_app_spec.spl
bin/simple test test/03_system/app/enterprise/store_web_harden_spec.spl
bin/simple test test/03_system/app/enterprise/enterprise_web_app_spec.spl
bin/simple test test/03_system/app/enterprise/back_office_web_spec.spl
bin/simple test test/03_system/app/enterprise/enterprise_auth_throttle_spec.spl
bin/simple test test/03_system/app/enterprise/enterprise_security_audit_spec.spl
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

## Out-of-suite reds in the `http_server` tier specs (found 2026-08-17, W10-A)

Enumerating the enterprise+http spec family from disk rather than from this
list turned up `*/http_server/*_spec.spl` files that the recorded suite never
ran. **RESOLVED 2026-08-17 (lane W14) — the table that used to sit here is
superseded and has been removed rather than left to mislead.** Read
`doc/09_report/verify/http_server_suite_enumeration_2026-08-17.md`; the
enumeration is now a glob (above) fenced by
`scripts/check/check-http-server-suite-enumeration.shs`.

What the old table got wrong, and it is worth knowing because the failure mode
recurs: it reported "9 RED, three orphaned against an API that does not exist"
and concluded a missing library API. The `git log -S` check confirms those
functions (`default_security_headers_config`, `default_rate_limit_config`, …)
never existed — but the specs had **already been repointed** at the real
class-based API (`SecurityHeadersConfig.default()`, `RateLimitConfig.default()`,
`CsrfConfig.default()`) by lane W11-A. The reds were measured against a shared
working copy holding an uncommitted revert to the phantom-API text. **The
library was fine; the checkout was stale.** Only `csrf_spec`'s mirror copy was
genuinely red at HEAD, and W14-A rewrote it (13/13).

Current measurement — 26 canonical specs plus the one divergent mirror, swept
one-per-process in a CLEAN WORKTREE at `origin/main` (never the shared
checkout, for exactly the reason above), Jul-25 aarch64 binary:

**25/27 files green — 290 examples, 275 passed, 15 failed, 0 missing verdicts.**

The only 2 reds are `chunked_body_boundary_spec` (7/14) and
`chunked_size_overflow_spec` (4/12), both the pre-existing `common_index_of`
aliased-import defect recorded in-tree at
`src/lib/nogc_async_mut/http_server/parser.spl:29`. Everything the old table
listed is now green, including `protocol_handler_spec` (8/8) and
`compression_spec` (20/20), fixed by lane W11-B.

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
10. **Never trust the recorded spec list as the enumeration.** The 48-file list
    in this doc silently omitted 21 `http_server` tier specs and predated
    `enterprise_security_audit_spec`. Enumerate from disk every sweep and diff
    against this list; a spec that appeared or vanished is itself a finding.

## Guides

- `doc/07_guide/lib/database/enterprise_store.md` (surface, backend honesty,
  failure-path hardening, cross-OS matrix, file backend, outbox worker)
- `doc/07_guide/app/enterprise/` — `store_app.md` (all route families incl.
  back-office + auth/throttle), `guarded_command_contract.md`,
  `replay_and_state_dependent_validation.md`, `booking.md`, `restaurant.md`,
  `payment.md`, `hcm.md`, `procurement.md`, `finance.md`, `channel_hub.md`
- `doc/07_guide/lib/networking/http_server_hardening.md`
- Assessment: `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`
