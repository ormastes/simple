# nogc_async_mut: specs import modules absent from src/lib

Date: 2026-09-16
Status: LIVE (triaged 2026-11-11, lane work/p3-rt3-20261111 — debug adapter half landed and green; http_server half still absent, owner named below)

## Observed

Five worklist specs fail at module resolution / export level because the
modules or exports they target do not exist anywhere under `src/lib`:

- `http_server/async_handler_lifecycle_spec.spl` — `std.http_server.async_handler_lifecycle` does not exist.
- `http_server/h2_async_dispatch_spec.spl` — `std.http_server.h2_async_dispatch` does not exist.
- `http_server/tls13_record_adapter_spec.spl` — `std.http_server.tls13_record_adapter` does not exist.
- `debug/coordinator_service_adapter_v1_spec.spl` — `std.nogc_async_mut.debug.coordinator_service_adapter_v1` missing.
- `debug/legacy_service_adapter_v1_spec.spl` — `std.nogc_async_mut.debug.legacy_service_adapter_v1` missing.

## Impact

`semantic: Module does not export X` / `Cannot resolve module` — the specs
cannot run at all; the features they pin have no implementation to verify.

## Expectation

Either the modules exist with the documented exports, or the specs are retired
together with the design that produced them.

## Unblock condition

Implement the five modules (or delete the specs with the owning team's sign-off
if the designs were superseded). Not spec-fixable: the files are absent from
`src/lib`.

---

## 2026-11-11 triage — lane rt3 (worktree simple-p3-rt3-20261111, base 7f0fa174083, seed 46fe8f6b6def)

**Verdict: LIVE (named owner) — 2 of 5 modules landed and verified green; the
http_server family is still absent and is substantive feature work.**

Fresh census + behavioral re-verification (tracked seed, interpreter):

**Landed, specs PASS (were module-resolution ERROR on 2026-09-16):**
- `std.nogc_async_mut.debug.coordinator_service_adapter_v1` —
  `src/lib/nogc_async_mut/debug/coordinator_service_adapter_v1.spl` present;
  `test/01_unit/lib/nogc_async_mut/debug/coordinator_service_adapter_v1_spec.spl`
  3/3 PASS.
- `std.nogc_async_mut.debug.legacy_service_adapter_v1` —
  `src/lib/nogc_async_mut/debug/legacy_service_adapter_v1.spl` present;
  `legacy_service_adapter_v1_spec.spl` 5/5 PASS.

**Still missing (specs still ERROR, executed=0):**
- `std.http_server.async_handler_lifecycle` — `src/lib/http_server/` does not
  exist at all; `http_server/async_handler_lifecycle_spec.spl` re-verified
  `outcome=ERROR declared>=4 executed=0`.
- `std.http_server.h2_async_dispatch` — same absence (spec
  `http_server/h2_async_dispatch_spec.spl` not re-run; same module-resolution
  failure class, same missing directory).
- `std.http_server.tls13_record_adapter` — same absence (spec
  `http_server/tls13_record_adapter_spec.spl` not re-run; same class).

Named owner: **http_server package lane** (implement
`async_handler_lifecycle`, `h2_async_dispatch`, `tls13_record_adapter` under
`src/lib/http_server/`, or retire the three specs with the owning lane's
sign-off per this record's unblock condition). No spec edited, no assertion
relaxed, no production change attempted in this lane.


## Triage 2026-11-13 (lane p3-async-20261113, base 80a8116e5e2) — still LIVE (http_server half), reproduced once

Reproduced once on this base (seed `bin/simple.exe`, `--timeout 300`):
`test/01_unit/lib/nogc_async_mut/http_server/async_handler_lifecycle_spec.spl`
→ `outcome=ERROR declared>=4 executed=0` —
`Module "std.http_server" does not export 'async_handler_lifecycle'`;
`src/lib/http_server/` still does not exist. `h2_async_dispatch` and
`tls13_record_adapter` remain the same absence class (not re-run). The two
debug adapters (`coordinator_service_adapter_v1`, `legacy_service_adapter_v1`)
are present on this base; the 2026-11-11 rt3 lane's 3/3 and 5/5 evidence
stands per the no-rerun rule.

Not fixed in this lane: implementing the three http_server modules is
substantive feature work owned by the http_server package lane (per this
record's unblock condition); the 20-minute P3 timebox cannot absorb it and no
spec was weakened. No source change.
