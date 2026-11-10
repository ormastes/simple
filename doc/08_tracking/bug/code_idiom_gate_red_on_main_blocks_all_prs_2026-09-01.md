# `Code Idiom & Structural Ratchet Gates` is RED on `main` — blocks every PR
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Date: 2026-09-01
- Status: OPEN — re-measured 2026-11-11 (lane ne4) on release/1.0.0 tip: UI backend-isolation gate now PASS (was offender 1); PID/clock-keyed artifact ratchet still FAIL with 8 new offenders (was 1); guard-wiring gate re-run in progress (see addendum). Not caused by any open PR remains the finding.
- Required check (ruleset `spipe-vcs-v3-main`, id 21573643): `Code Idiom & Structural Ratchet Gates`
- Workflow: `.github/workflows/repo-hygiene.yml`, job `code-idiom-gates`

## Evidence of pre-existence

| where | run / job | verdicts |
|---|---|---|
| `main` tip `1b12bd36b` | run `33486779024`, job `99788604481` | same 3 gates FAIL |
| PR #252 head `477d446129e` | run `33488592730`, job `99794430241` | same 3 gates FAIL, byte-identical offender lines |

PR #252 touches 9 files (7 `src/lib/**`, 1 spec, 1 doc). **None** of the three
offenders is among them, and the offender lines are identical on `main`.
Verdict: PR-caused = NO. Pre-existing on `main` = YES.

## The three failing steps (verbatim)

1. **UI backend-isolation ratchet gate** — `scripts/check/check-ui-backend-isolation.shs`
```
ui_backend_isolation_new_violation=RT:examples/09_embedded/simple_os/arch/riscv64/wm_vulkan_smoke_entry.spl
examples/09_embedded/simple_os/arch/riscv64/wm_vulkan_smoke_entry.spl:34:extern fn rt_mmio_write_u32(addr: u64, value: u32)
examples/09_embedded/simple_os/arch/riscv64/wm_vulkan_smoke_entry.spl:60:            rt_mmio_write_u32(base + off.to_u64(), argb)
ui_backend_isolation_baselined=30
ui_backend_isolation_current=31
ui_backend_isolation_new=1
ui_backend_isolation_ok=false
```

2. **Guard-wiring ratchet gate** — `scripts/check/check-guard-wiring.shs`
```
check-guard-wiring: FAIL — 1526 guard(s) checked, 14 NEW unwired (743 baselined as known debt), 2 stale/bad baseline or opt-out line(s), 0 copied hook(s)
```
14 NEW unwired guards:
`check-freestanding-byte-array-slot-tags.shs`,
`check-freestanding-dict-arms-in-every-definition.shs`,
`check-freestanding-dict-write-path.shs`,
`check-freestanding-rt-value-int-tags.shs`,
`check-prepush-no-recursion.shs`,
`check-simpleos-arm64-wm-vulkan-pixel-evidence.shs`,
`check-simpleos-dbfs-server-roundtrip-ovmf.shs`,
`check-simpleos-nvfs-server-roundtrip-ovmf.shs`,
`check-simpleos-riscv64-components-in-guest-opensbi.shs`,
`check-simpleos-riscv64-interpreter-in-guest-opensbi.shs`,
`check-simpleos-riscv64-wm-render-smoke-opensbi.shs`,
`check-simpleos-x86-64-components-in-guest-ovmf.shs`,
`repro-selective-vs-whole-import.shs`,
`run-riscv64-text-probe-opensbi.shs`.

2 stale baseline entries (now wired — delete their lines in
`scripts/check/` unwired baseline):
`check-dual-run-shadow.shs`, `check-unbacked-extern-ratchet.shs`.

3. **PID/clock-keyed build artifact ratchet**
```
FAIL — 34 candidate(s) checked in /home/runner/work/simple/simple; NEW pid/clock-keyed build artifact(s): src/compiler/70.backend/backend/runtime_compiler.spl
```

## Why this blocks everything

The ruleset requires this check on every merge to `main`. Because it is red on
`main` itself, **no PR can ever go green** until the three offenders above are
fixed on `main`. The debt is owned by whoever landed the offending files, not
by the PR authors it now blocks.

Explicitly NOT done here: no baseline was regenerated. Per
`.claude/rules/vcs.md`, `--generate-baseline` is for reviewed updates only;
using it to clear a red is how a ratchet silently stops ratcheting.

## Cross-platform impact

None. This is a CI-configuration/debt record; no source was changed, so Windows
and Unix behaviour are both unaffected.


## 2026-11-11 addendum (lane ne4, batch p3-ne4-20261111)

The three named offenders re-measured on release/1.0.0 tip
(fa6366ca8bf5 + lane commits) in this worktree:

1. **UI backend-isolation ratchet** (`scripts/check/check-ui-backend-isolation.shs`)
   — **PASS / FIXED**: `ui_backend_isolation_new=0`,
   `baselined=28, current=28, ok=true, RC=0`. The
   `riscv64/wm_vulkan_smoke_entry.spl` offender is gone from the new set
   (baseline now 28).

2. **PID/clock-keyed build artifact ratchet**
   (`scripts/check/check-no-pid-keyed-build-artifacts.shs`) — **FAIL, grown**:
   `FAIL — 44 candidate(s) checked; NEW pid/clock-keyed build artifact(s):
   src/app/cli/native_build_main.spl,
   src/compiler/80.driver/cache/daemon/cache_daemon_queue_v1.spl,
   src/compiler/80.driver/driver_build/native_file_worker_incremental_io_v1.spl,
   src/compiler/80.driver/driver_build/native_link_receipt_v1.spl,
   src/compiler/80.driver/driver_build/smf_object_spool_v1.spl,
   src/compiler/80.driver/driver_ice_boundary.spl,
   src/compiler/80.driver/driver_native_prelower_cache.spl,
   src/compiler/80.driver/driver_xray_link.spl` (filing: 1 offender).
   Per-line classification against the gate's own documented intent:
   - durable pid-keyed artifact paths (genuinely keyed): xray
     `xray_native_runtime_{isa}.{getpid()}.o` (driver_xray_link.spl:88),
     smf spool `"{root}/p{getpid()}"` (smf_object_spool_v1.spl:126),
     ice cache key `"{getpid()}_{hash}"` (driver_ice_boundary.spl:207),
     native-build stderr spill logs `native-build-stderr-{getpid()}-{seq}.log`
     (native_build_main.spl:654).
   - collision-avoidance renames / staging dirs matching the gate's own
     documented exception class but not its exclusion patterns:
     trash rename `".{getpid()}"` (cache_daemon_queue_v1.spl:90),
     `reuse.{getpid()}` marker (native_file_worker_incremental_io_v1.spl:156),
     `.{getpid()}.old` + `.link-tmp-{getpid()}` (native_link_receipt_v1.spl:306,347),
     `.stage-{getpid()}-` (driver_native_prelower_cache.spl:245),
     `ice_receipt.{getpid()}.part` / breadcrumbs (driver_ice_boundary.spl:103,107).
   - external-process probes, not artifact keying at all:
     `/proc/{pid}/exe`, `ps -p {pid}` (native_build_main.spl:136,142).
   Unblock: compiler/driver-owner decisions per file (de-key the durable
   paths; widen the gate's exclusion patterns for the staging/probe class;
   reviewed baseline update for the rest). Not done in this lane: the
   baseline is a reviewed-update control and several candidates need owner
   intent, not mechanical edits.

3. **Guard-wiring ratchet** (`scripts/check/check-guard-wiring.shs`) —
   re-run 2026-11-11 on this Windows host; the full-tree reference scan
   (2016 guard paths x ~1694 reference files) did not complete within the
   lane's time budget (ran >40 min; selftest 43/43 fixtures passed before
   the scan). Filing numbers stand: 14 NEW unwired, 2 stale baselines.
   The independently re-derived wiring delta over the same registry is
   tracked by the lane's vacuity re-derivation (59/201 gates without
   em-dash verdicts), which is the same debt class from the surface
   direction.

Also in this lane: the `rules.sdl` digest-binding gate
(`check-rules-sdl.shs --group quick`, same CI hygiene family) was
ERROR-red on tip because merged commit abb2fe62cc64 changed rules.sdl
without re-binding the reviewed digest or lowering the
`rules_sdl_gates` floor; repaired in commit 282ffdb2ab8b (gate now
`PASS — 10 gates checked, 0 shrank`, selftest 7/7 fixtures).

Verdict: LIVE. The "red on main blocks every PR" thesis holds for the
ratchet family on this tree: one offender fixed, one grown (8 rows),
one re-run pending. All red is real debt, no guard-text defect found in
the two gates that completed.
