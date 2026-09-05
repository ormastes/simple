# MC/DC and RT/HAL feature expert

Use this page when changing MC/DC instrumentation, `@rt(hal)` lowering/provider
comparison, or RT/HAL environment evidence.

## Non-negotiable architecture

- MC/DC has three modes: static off (no probe, allocation, registration,
  dispatch, or loader route), static on (fixed owner-local recorder), and
  dynamic aspect (one dormant branch/token; activation and unload are cold).
- Preserve evaluation order/count and short-circuit behavior. Record only after
  an expression is evaluated; do not reevaluate user code for coverage.
- Normal and stricter profiles require exact `covered == required`. Exclusions
  are condition-scoped, stable-identity records with technical reason, reviewer,
  review ID, and expiry/version; they are reported separately and never become
  a passing generic skip.
- Pure Simple remains the semantic/effect owner. C/Rust are typed comparators:
  they receive canonical input or replay data and never repeat irreversible I/O.
- `@rt(hal)` defaults to mission-critical unless explicitly profiled. Critical
  hot paths fail closed on unproved allocation, blocking, recursion, dynamic
  dispatch, loader work, unbounded logging, or synchronization.
- Live RT/HAL setup is compiler-owned sealed V3. Public V2 and direct V3 setup
  reject; canonical full-plan identity prevents Plan B from reusing Plan A.
- All RT/HAL interaction is a bounded `EnvAccessPlan` owned by app I/O. The
  closed 24-kind vocabulary is physical only through a sealed adapter; missing
  host/hardware evidence is `Blocked`/`Unsupported`, not PASS.

## Evidence workflow

Use `doc/03_plan/sys_test/mcdc_rt_hal_hardening.md` as the traceability owner,
`doc/07_guide/compiler/mcdc_rt_hal.md` as the operator guide, and
`test/05_perf/mcdc_rt_hal/` for identical-fixture performance receipts. Keep
executable scenarios in `test/` and their manuals in `doc/06_spec/`; never put
`*_spec.spl` under `doc/06_spec`.

Run a criterion once with the admitted self-hosted runtime only. Retain exact
static-off artifact inventory, normal-mode report, C/Rust parity/effect replay,
all environment receipts, timing, peak RSS, allocation/copy counters, and
optimizer receipts. No seed, manual, source inspection, or blocked host row is
release evidence. If the runtime is unavailable, update the plan and manuals as
unverified and retain the exact resume command; do not convert blocked work to a
skip.

## Source anchors

- MC/DC lowering: `src/compiler/50.mir/mir_lowering_stmts.spl`
- Dynamic probe: `src/lib/nogc_sync_mut/mcdc/dynamic_probe.spl`
- Exact gate: `src/compiler/00.common/mcdc_coverage_gate.spl`
- RT/HAL staging: `src/compiler/50.mir/rt_hal_stage_test_seam.spl`
- Host and plan identity: `src/app/io/rt_hal_isolated_host.spl`
- Environment model/SDN/host: `src/lib/common/env_access/`, `src/app/io/env_access_host.spl`
