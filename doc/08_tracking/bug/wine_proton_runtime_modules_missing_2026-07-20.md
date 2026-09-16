# wine_proton_runtime_spec.spl: `common.wine_proton_gate` / `common.wine_proton_runtime` modules do not exist

**Status:** Open
**Category:** GENUINE-BUG (missing implementation, not a stale rename)
**Discovered:** 2026-07-20 (whole-suite triage campaign, shard meas_01u_03)

Same defect class as `wine_seh_frame_module_missing_2026-07-20.md` (filed
same shard): a Wine-compatibility spec imports modules that were never
implemented anywhere under `src/`.

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 25 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/lib/common/wine_proton_runtime_spec.spl --no-session-daemon
```

```
error: semantic: Cannot resolve module: common.wine_proton_gate

error: test-runner: no examples executed

Passed: 0
Failed: 1
FAIL test/01_unit/lib/common/wine_proton_runtime_spec.spl
```

## Spec imports (test/01_unit/lib/common/wine_proton_runtime_spec.spl:1-8)

```
use common.wine_proton_gate.{wine_proton_fixture_wine_gates}
use common.wine_proton_runtime.{
    wine_proton_fixture_runtime_evidence,
    wine_proton_runtime_evidence_new,
    wine_proton_runtime_feature_evidence,
    wine_proton_runtime_gate,
    wine_proton_runtime_readiness_gate
}
```

Neither `src/lib/common/wine_proton_gate.spl` nor
`src/lib/common/wine_proton_runtime.spl` (nor any file of those names
anywhere under `src/`) exists. None of the 6 imported symbols, nor any of the
gate-string literals the spec asserts against
(`"missing-steam-runtime"`, `"missing-abi-x86_64"`,
`"missing-steam-linux-runtime-generation"`, `"missing-container-rootfs"`,
`"missing-container-rootfs-nvfs"`, `"missing-namespace-capability"`,
`"missing-dxvk"`, `"missing-steamworks-bridge"`,
`"blocked-wine-blocked-missing-vm"`, `"ready"`), appear anywhere in the
source tree.

Two adjacent-but-distinct modules DO exist and cover related ground —
`src/lib/nogc_async_mut/steam/steam_runtime.spl` (Steam runtime ABI
detection: `_sri_ok`, `_sri_err`, `_sr_has_token`) and
`src/os/game/platform/compatibility_contract.spl` (generic game-target
readiness gating: `game_target_proton_x86`, `game_target_ready`,
`game_target_blocker`, etc.) — but neither defines the specific
`wine_proton_*` symbol names or the granular Proton-launch gate strings
(Steam Runtime -> pressure-vessel container -> Vulkan/DXVK/VKD3D-Proton ->
Steamworks bridge escalation) this spec expects. This is not a simple
rename target.

## Why not classified STALE-TEST

No current API exists to migrate the spec onto; the entire two-module
surface (fixture builders, evidence constructor, 3-stage gate function,
feature-string deriver, readiness-gate combiner) would need to be
implemented from scratch. That's out of scope for this triage pass (src/**
edits are restricted to unambiguous one-line import/rename fixes only).

## Suggested fix

Either implement `src/lib/common/wine_proton_gate.spl` and
`src/lib/common/wine_proton_runtime.spl` per the 6 `it` blocks' expectations
(likely by layering Proton/Steamworks/DXVK gate logic on top of the existing
`steam_runtime.spl` and `compatibility_contract.spl` primitives), or — if the
feature was deliberately not pursued — delete the orphaned spec (requires
explicit user approval per project rules; not done here).

## Affected specs

- `test/01_unit/lib/common/wine_proton_runtime_spec.spl` (sole affected spec in this shard)
