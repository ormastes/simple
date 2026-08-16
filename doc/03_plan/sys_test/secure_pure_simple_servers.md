<!-- codex-design -->
# Secure Pure-Simple Servers System Test Plan

## Executable and mirrored artifacts

- Web: `test/03_system/web/server/secure_pure_simple_web_server_spec.spl`
  -> `doc/06_spec/03_system/web/server/secure_pure_simple_web_server_spec.md`
- Shared HTTP policy regression support:
  `test/01_unit/lib/common/net/http_core_spec.spl`
  -> `doc/06_spec/01_unit/lib/common/net/http_core_spec.md`
- DB tier: `test/03_system/database/server/db_server_tier_spec.spl`
  -> `doc/06_spec/03_system/database/server/db_server_tier_spec.md`
- DB durability: `test/03_system/database/server/db_durability_spec.spl`
  -> `doc/06_spec/03_system/database/server/db_durability_spec.md`

All named Markdown mirrors currently exist. Their presence is not a generated
receipt: current `sspec-maintain` scorecards, docgen output, zero-stub evidence,
and operator review remain blockers. Do not add executable specs below
`doc/06_spec`.

## Scenario matrix

| Scenario/oracle | REQ / AC | Evidence |
|---|---|---|
| Real loopback request reaches route, identity, headers, writer | REQ-001 / AC-1 | exact response + route count |
| Boundary and boundary+1 request limits reject before route | REQ-002 / AC-2 | exact status + zero route count |
| Framing/header/coding/traversal matrix rejects | REQ-002 / AC-2 | exact class + zero route count |
| Missing/invalid TLS refuses; explicit dev plaintext works | REQ-003 / AC-3 | startup result; partial only |
| Encrypted handshake carries HTTP without downgrade | REQ-003 / AC-3 | real TLS client response; blocked GAP-TLS-3 |
| DB bind, capacity rejection, disconnect cleanup, shutdown/rebind, post-stop accept rejection | REQ-004 / AC-4 | counts + bind probe + empty post-stop response |
| Missing/unknown/wrong credential are indistinguishable | REQ-005 / AC-5 | exact equal responses + no secret capture |
| Peer reader cannot observe P3/P4 | REQ-006 / AC-6 | independent peer values before/after |
| Conflict token survives close/reopen | REQ-007 / AC-7 | reopened conflict result |
| Lost acknowledgement retry does not reapply | REQ-007 / AC-7 | reopened value/version/applied count |
| Batch/range capability, overlay, order, exact bounds | REQ-008 / AC-8 | exact list/value and no partial mutation |

Continuation truth (2026-08-16): the working tree contains an unexecuted real
loopback DB bind/OPEN/EOF/cleanup/rebind scenario and an adjacent UTF-8 parser
oracle. It also contains unexecuted synchronous web fixes for rejecting every
unsupported transfer coding and bounding complete response writes. None is a
PASS until the exact focused commands below execute on an admitted Stage-4
self-hosted CLI. Production TLS remains blocked independently by GAP-TLS-3.

REQ-009..REQ-014 are verified by the evidence audit, not synthetic behavior
tests: deliberate-red calibration; one `sspec-maintain scan` per changed spec;
docgen zero stubs; REQ links; static/focused/full gates; final review receipt;
commit, locked integration, refetch/reachability, and clean-tree proof.

## Manual presentation

Show the seven accepted operator steps as the primary flow. Hide reusable setup
with `@inline`, connect prerequisite state with `@prev`, fold matrices/stress
details, and retain API/protocol/exec captures. Assertions use built-in
matchers only and absolute values. Helpers without a valid oracle must call
`fail(...)` or `assert(false)`.

## Execution discipline

Calibrate each new oracle deliberately red before crediting its green result.
Verify each criterion once in this session and permit at most three fix cycles.
Run focused specs before broader checks. The whole interpreter suite is a
release-bound gate only after a healthy Stage-4 self-hosted CLI exists. Record
TLS GAP-TLS-3 and unhealthy CLI as WARN/blockers; neither may be called PASS.

## Exact deferred verification order

Do not run this block until `ADMITTED_STAGE4_SIMPLE` names the exact full
self-hosted CLI accepted by its adjacent provenance/admission receipt. Record
its absolute path and SHA-256. Run each unchanged command once, in this order:

```sh
"$ADMITTED_STAGE4_SIMPLE" check src/lib/common/net/http_core.spl
"$ADMITTED_STAGE4_SIMPLE" check src/lib/nogc_sync_mut/http_server
"$ADMITTED_STAGE4_SIMPLE" check src/lib/nogc_sync_mut/database/server
"$ADMITTED_STAGE4_SIMPLE" test test/01_unit/lib/common/net/http_core_spec.spl --mode=interpreter
"$ADMITTED_STAGE4_SIMPLE" test test/01_unit/lib/http_server/chunked_rejection_spec.spl --mode=interpreter
"$ADMITTED_STAGE4_SIMPLE" test test/03_system/web/server/secure_pure_simple_web_server_spec.spl --mode=interpreter
"$ADMITTED_STAGE4_SIMPLE" test test/03_system/database/server/db_server_tier_spec.spl --mode=interpreter
"$ADMITTED_STAGE4_SIMPLE" test test/03_system/database/server/db_durability_spec.spl --mode=interpreter
"$ADMITTED_STAGE4_SIMPLE" test test/03_system/database/server/secure_pure_simple_db_server_spec.spl --mode=interpreter
"$ADMITTED_STAGE4_SIMPLE" test test/03_system/os/simpleos_riscv_network_gate_spec.spl --mode=interpreter
"$ADMITTED_STAGE4_SIMPLE" sspec-maintain scan test/01_unit/lib/http_server/chunked_rejection_spec.spl
"$ADMITTED_STAGE4_SIMPLE" sspec-maintain scan test/03_system/web/server/secure_pure_simple_web_server_spec.spl
"$ADMITTED_STAGE4_SIMPLE" sspec-maintain scan test/03_system/database/server/db_server_tier_spec.spl
"$ADMITTED_STAGE4_SIMPLE" sspec-maintain scan test/03_system/database/server/db_durability_spec.spl
"$ADMITTED_STAGE4_SIMPLE" sspec-maintain scan test/03_system/database/server/secure_pure_simple_db_server_spec.spl
"$ADMITTED_STAGE4_SIMPLE" sspec-maintain scan test/03_system/os/simpleos_riscv_network_gate_spec.spl
"$ADMITTED_STAGE4_SIMPLE" spipe-docgen test/01_unit/lib/http_server/chunked_rejection_spec.spl --output doc/06_spec --no-index
"$ADMITTED_STAGE4_SIMPLE" spipe-docgen test/03_system/web/server/secure_pure_simple_web_server_spec.spl --output doc/06_spec --no-index
"$ADMITTED_STAGE4_SIMPLE" spipe-docgen test/03_system/database/server/db_server_tier_spec.spl --output doc/06_spec --no-index
"$ADMITTED_STAGE4_SIMPLE" spipe-docgen test/03_system/database/server/db_durability_spec.spl --output doc/06_spec --no-index
"$ADMITTED_STAGE4_SIMPLE" spipe-docgen test/03_system/database/server/secure_pure_simple_db_server_spec.spl --output doc/06_spec --no-index
"$ADMITTED_STAGE4_SIMPLE" spipe-docgen test/03_system/os/simpleos_riscv_network_gate_spec.spl --output doc/06_spec --no-index
"$ADMITTED_STAGE4_SIMPLE" duplicate-check src/lib/nogc_sync_mut/http_server --mode token --min-lines 5
"$ADMITTED_STAGE4_SIMPLE" duplicate-check src/lib/nogc_sync_mut/database/server --mode token --min-lines 5
"$ADMITTED_STAGE4_SIMPLE" deps deep src/lib/nogc_sync_mut/http_server/server.spl
"$ADMITTED_STAGE4_SIMPLE" deps deep src/lib/nogc_sync_mut/database/server/server.spl
sh scripts/audit/numbered-artifact-guard.shs --working
sh scripts/audit/numbered-artifact-guard.shs --staged
sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --staged
find doc/06_spec -name '*_spec.spl' -print
"$ADMITTED_STAGE4_SIMPLE" test test --whole --mode=interpreter
```

Run lint once on the exact owned changed `.spl` list after the web/DB sidecars
settle; retain that explicit file list in the receipt. The layout command must
print no paths. Run the whole suite only after all focused commands and manual
review pass; it does not repair a focused failure.
