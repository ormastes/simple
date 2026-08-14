<!-- codex-design -->
# Secure Pure-Simple Servers System Test Plan

## Executable and mirrored artifacts

- Web: `test/03_system/web/server/secure_pure_simple_web_server_spec.spl`
  -> `doc/06_spec/03_system/web/server/secure_pure_simple_web_server_spec.md`
- DB tier: `test/03_system/database/server/db_server_tier_spec.spl`
  -> `doc/06_spec/03_system/database/server/db_server_tier_spec.md`
- DB durability: `test/03_system/database/server/db_durability_spec.spl`
  -> `doc/06_spec/03_system/database/server/db_durability_spec.md`

Missing mirrored DB manuals or missing scenarios are blockers, not waived
coverage. Do not add executable specs below `doc/06_spec`.

## Scenario matrix

| Scenario/oracle | REQ / AC | Evidence |
|---|---|---|
| Real loopback request reaches route, identity, headers, writer | REQ-001 / AC-1 | exact response + route count |
| Boundary and boundary+1 request limits reject before route | REQ-002 / AC-2 | exact status + zero route count |
| Framing/header/coding/traversal matrix rejects | REQ-002 / AC-2 | exact class + zero route count |
| Missing/invalid TLS refuses; explicit dev plaintext works | REQ-003 / AC-3 | startup result; partial only |
| Encrypted handshake carries HTTP without downgrade | REQ-003 / AC-3 | real TLS client response; blocked GAP-TLS-3 |
| DB bind, capacity rejection, disconnect cleanup, shutdown/rebind | REQ-004 / AC-4 | counts + bind probe |
| Missing/unknown/wrong credential are indistinguishable | REQ-005 / AC-5 | exact equal responses + no secret capture |
| Peer reader cannot observe P3/P4 | REQ-006 / AC-6 | independent peer values before/after |
| Conflict token survives close/reopen | REQ-007 / AC-7 | reopened conflict result |
| Lost acknowledgement retry does not reapply | REQ-007 / AC-7 | reopened value/version/applied count |
| Batch/range capability, overlay, order, exact bounds | REQ-008 / AC-8 | exact list/value and no partial mutation |

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
