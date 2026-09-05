# WM evidence/lifecycle continuation tracker

Updated: 2026-08-20

## Source-owned slice completed

`WmService` remains the only mutable owner of lifecycle generation, scene
revision, ownership, focus, ingress bounds, and presentation receipt state.
`commit_presentation` now requires:

- the current lifecycle generation and scene revision;
- nonzero frame and readback identities; and
- an explicit authoritative readback source: `framebuffer` or
  `device_readback`.

Unspecified, synthetic, CPU-mirror, or other readback sources are rejected.
The accepted source is retained with the generation/revision/frame/hash tuple
and is cleared by restart. `presentation_matches` compares the complete tuple,
including source provenance.

Behavioral coverage is in
`test/01_unit/os/services/wm/wm_service_lifecycle_hardening_spec.spl`, covering
zero IDs, invalid source, source mismatch, stale revision, stale frame,
restart clearing, nonzero authoritative receipts, and deterministic focus-stack
raise/remove/fallback behavior. The owner now admits bounded
`WmDamageRegionV1` candidates into a generation/revision-correlated
`WmRedrawDecisionV1`; focus raise, content/geometry/state changes, owner-death
exposure, and window creation enqueue redraw state, while a committed
presentation clears it. This is a structured source contract only.

## Source layout guard

The public import path remains `src/os/services/wm/wm_service.spl`. The
canonical mutable `WmService` owner is defined once in
`wm_service_core.spl`; protocol/IPC methods are an extension in
`wm_service_protocol.spl` and add no mutable state. Pure damage admission is
in `wm_damage.spl`, with its owner-field projection in
`wm_damage_owner.spl`. All five files are kept below the 800-line source
limit so the façade stays stable without creating a parallel WM owner. Codec helpers and core protocol constants use
`pub(package)`; the façade exposes only `WmService`, `WmAction`, the launch
notification, and the frozen damage/redraw contract. `WmService` also owns a bounded focus stack: focus
raises a window deterministically, owner removal removes it, and fallback is
the smallest surviving window.

## Evidence status

| Row | Status | Truthful boundary |
|---|---|---|
| WmService receipt validation | STATIC-PASS | Source-owned contract and negative behavioral spec are present; no runtime claim is made in this lane. |
| x86_64 QEMU desktop/readback | BLOCKED | Requires an admitted runnable self-hosted runtime and a fresh nonce-bound guest receipt. |
| AArch64 QEMU/physical visual capture | BLOCKED | Requires booted target evidence plus identified framebuffer/JTAG or capture-device readback. |
| RV64 QEMU/physical visual capture | BLOCKED | Requires booted target evidence plus identified framebuffer/JTAG or capture-device readback. |
| Native/physical WM performance | BLOCKED | Requires ten-sample native evidence with p95/p99/RSS and input-to-present correlation. |

No screenshot, CPU mirror, synthetic handle, QMP substitution, or source scan is
promoted as a WM PASS. `SimpleOsEvidenceReceiptV1` and
`SimpleOsCapabilityLedgerV1` remain the shared evidence/ledger owners; this
slice only supplies a validated WM receipt boundary for their future runner.

## Resume gate

After the pure-Simple runtime is admitted, run the focused unit spec once, then
the canonical WM campaign:

```text
bin/simple test test/01_unit/os/services/wm/wm_service_lifecycle_hardening_spec.spl --mode=interpreter
bin/simple test test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.spl --mode=interpreter
```

The campaign remains blocked until its checker consumes real DrawIrComposition
-> Engine2D -> framebuffer/readback artifacts and publishes a fresh shared
receipt. Physical rows additionally require board/display/capture identity and
must not inherit QEMU status.
