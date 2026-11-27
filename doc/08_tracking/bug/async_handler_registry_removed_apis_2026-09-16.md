# Async-handler registry APIs removed; contract specs still pin them

Date: 2026-09-16
Status: FIXED 2026-11-13 (lane p3-asyncreg-20261113) — APIs restored 2026-11-05 (work/libbug-async-registry-20261105, `8dcf70e1ffd`); restored drain loop made ERR-01-clean 2026-11-13; bug_db row flipped to `fixed`

## Observed

`http_server/async_handler_registry_spec.spl` and
`http_server/async_ssr_disconnect_safety_contract_spec.spl` pin the removed
async-handler design: `async_job_by_fd` (e.g. source pin
`self.async_job_by_fd[fd] = job_id`), `submit_async_handler`,
`register_async`. None of these symbols exist anywhere in `src/lib` (verified
by tree grep); the http_server was rewritten around
`worker_owner.spl`/`worker_connection_extensions.spl` and driver cancellation
now goes through different paths (`self.driver.cancel_fd(fd)` also absent).

## Impact

The two contract specs fail on text-scan contains-checks; the safety property
they documented (exactly-once async cancellation, per-fd job identity) has no
current implementation to pin.

## Expectation

Either the async-handler registry is restored, or the specs are rewritten
against the successor mechanism once that mechanism exposes an equivalent
cancellation contract.

## Unblock condition

Owner decision: re-implement per-fd async job tracking, or replace the specs'
pins with the worker-runtime equivalents. Not an easy spec-side fix (assertions
pin real removed behavior).

## Resolution (2026-11-05, work/libbug-async-registry-20261105)

Owner decision taken: per-fd async job tracking re-implemented (async-first,
no blocking sync wrappers).

- `src/lib/nogc_async_mut/http_server/worker.spl` is no longer a pure
  export facade: it now owns the `impl Worker` async-handler registry
  extension — `submit_async_handler` / `complete_async_handler` /
  `cancel_async_handler` (exactly-once, per-fd job identity via
  `self.async_job_by_fd[fd] = job_id`), `park_async_response`,
  `submit_async_location`, `deliver_async_completion` — plus
  `close_connection` / `close_all_connections`, moved here from
  `worker_connection_extensions.spl`. An observed close revokes the
  pending job via `self.cancel_async_handler(fd)` and drops in-flight
  socket operations via `self.driver.cancel_fd(fd)` before teardown.
- `worker_owner.spl`: Worker state (`async_job_by_fd`, `async_channel_by_fd`,
  `async_fd_by_job`, `async_response_by_job`, `async_inbox`, `async_job_seq`),
  an async-first branch in `process_request` (async-admitted handler types
  submit a typed job and park the connection; rejection fails closed 503
  "Async handler service unavailable"), and a bounded completion-inbox drain
  in the run loop.
- `worker_connection_extensions.spl`: `release_fd_operations` no longer
  cancels the fd itself; `close_h2_connection` now owns its explicit
  `self.driver.cancel_fd(fd)`.
- Both pinned specs pass:
  `async_ssr_disconnect_safety_contract_spec.spl` 3/3 (was 1/3);
  `async_handler_registry_spec.spl` 2/2 (registry APIs were already
  restored on release/1.0.0). Neighboring async specs re-run: no
  regressions. Worker exactly-once admit/complete/cancel semantics
  verified at runtime against a live `Worker` owner.
- Follow-up still open under the separate facade-split bug
  (`worker_spl_facade_split_breaks_source_contract_specs_2026-09-15.md`):
  `worker_registry_route_contract_spec.spl` (0/6) and
  `async_ssr_peer_probe_contract_spec.spl` (0/2) remain RED; they pin
  additional worker/driver source markers (`admit_http1_connection`,
  `rt_io_tcp_probe_peer`) outside this bug's scope. The
  `async_handler_lifecycle` module pinned by
  `async_handler_lifecycle_spec.spl` is still absent (0 executed).

## Closed 2026-11-09 (verification-only, lane p3-subj7)

Both pinned contract specs pass with the seed interpreter on
origin/release/1.0.0 (worktree @54181f128ea), matching the 2026-11-05
resolution note: `async_handler_registry_spec.spl` 2/2,
`async_ssr_disconnect_safety_contract_spec.spl` 3/3
(`--mode=interpreter --clean --timeout 120 --sequential`).
Neighbours green: worker_async_fd_registry 1/1, async_dynamic_dispatch 6/6.
Follow-up rows tracked separately (worker_spl_facade_split,
async_handler_lifecycle) remain open and were not touched. No source change
in this closure.

## Triage 2026-11-11 (lane p3-ne20) — verdict: SUPERSEDED (absorber named)

The 2026-11-09 p3-subj7 closure below left this header at `Status: OPEN`;
this lane flips it. Fresh source re-verification on origin/release/1.0.0
(worktree @9202f187777), not resting on the prior addendum alone:
`src/lib/nogc_async_mut/http_server/worker.spl:17` defines
`submit_async_handler(fd, job_id, ...)` and :28 carries the exact pinned
source marker `self.async_job_by_fd[fd] = job_id`; the per-fd registry
extension the two specs pin is present in-tree. The 2026-11-09 verification
(`async_handler_registry_spec.spl` 2/2, `async_ssr_disconnect_safety_contract_spec.spl`
3/3 on the seed interpreter) is 2 days old and same-branch; per the no-rerun
rule it is not re-executed.

Absorbers: implementation `work/libbug-async-registry-20261105` (resolution
section above) + verification lane p3-subj7 (2026-11-09). Follow-up rows
(worker_spl_facade_split, async_handler_lifecycle) are tracked separately and
untouched. Lane evidence: `build/review/p3fix-ne20-20261111.sdn`.


## Triage 2026-11-13 (lane p3-async-20261113, base 80a8116e5e2) — confirms SUPERSEDED

Same-base structural re-verification (no verdicted spec re-run, per no-rerun
rule): `src/lib/nogc_async_mut/http_server/worker.spl:17` defines
`submit_async_handler(fd, job_id, ...)` and `:28` carries the pinned marker
`self.async_job_by_fd[fd] = job_id`; the per-fd registry both contract specs
pin is present in-tree on this base. The 2026-11-09 verification evidence
(2/2 + 3/3, seed interpreter, same branch) stands. No source change.

## Resolution 2026-11-13 (lane p3-asyncreg-20261113, base f7cb252dce1) — FIXED

**Decision: accidental removal → restore (not "update specs to a new API").**
Evidence from history:
- PR #6804 (merged into release/1.0.0 on 2026-11-05, merge `d4798635325`, title
  "fix(http_server): restore per-fd async handler registry extension on Worker")
  and its commit `8dcf70e1ffd` ("restore per-fd async handler registry with
  exactly-once cancellation") put the APIs back. `git log -S'async_job_by_fd[fd] = job_id' -- src/lib`
  shows only that commit. No ADR, design doc or commit message retires the
  registry. The loss happened as a side-effect of the worker.spl facade split
  (`worker_spl_facade_split_breaks_source_contract_specs_2026-09-15.md`), not as
  a stated design change. The 2026-11-05 section above records the owner's
  decision to re-implement. The spec docstrings (`worker_async_fd_registry_spec.spl`)
  pin PR #6804 as the contract. No spec was rewritten or skipped.

**Remaining defect found and fixed in this lane.** The restored code did not
lower under the current seed. Seed fix `349cd121b82` (2026-11-09, ERR-01
nil-only-in-unsafe) now rejects `T? as <numeric>` outside `unsafe`. The
registry's completion drain in `worker_owner.spl` did `async_msg as i64` on
`Channel.try_recv() -> T?`. `embedded.spl` did `fd_opt as i64` on
`Dict<i64,i64>.get`. Both made the whole `std.http_server` package fail HIR
lowering, so every spec that constructs a live `Worker` executed 0 examples.
Fix (narrowing, no default/sentinel, no nil widening):
- `worker_owner.spl`: `val async_msg: i64? = self.async_inbox.try_recv()` then
  `if val async_job_id = async_msg:` … `else: break`.
- `embedded.spl`: `if val fd = op_to_fd.get(op_id):`.

Compiler gap noted (not fixed here; filed as `if_val_binding_from_generic_optional_stays_optional_err01_2026-11-13`): `if val m = ch.try_recv()` followed by
`m as i64` still trips ERR-01. The `if val` binding from a generic `T?` return
stays optional, even though the ERR-01 diagnostic recommends `if val`. A typed
`i64?` binding first works.

**Counts** (seed `seed-fix`, default mode, `MemoryMax=16G timeout 900`):

| spec | before (base f7cb252dce1) | after |
|---|---|---|
| async_handler_registry_spec | 2/2 | 2/2 |
| async_ssr_disconnect_safety_contract_spec | 3/3 | 3/3 |
| worker_async_fd_registry_spec | 0 executed (ERR-01) | 1/1 |
| async_dynamic_dispatch_spec | 0 executed (ERR-01) | 6/6 |
| worker_wire_shutdown_spec | 0 executed (ERR-01) | 10/10 |

Whole `test/01_unit/lib/nogc_async_mut/http_server/` (31 files): base 20 files
green / 175 passed. After: 23 files green / 192 passed. 0 regressions.
Still red on both sides, out of scope, with their own rows or causes:
async_handler_lifecycle (module absent), async_ssr_peer_probe_contract and
worker_registry_route_contract (facade-split bug), h2_async_dispatch
(`std.http_server.h2_async_dispatch` does not resolve), h2_live_socket_acceptance,
static_file_compression_cache (7/8), static_file_handler_compression (9/11),
tls13_record_adapter.
