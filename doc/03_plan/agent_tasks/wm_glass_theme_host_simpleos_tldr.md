# WM Glass Theme Agent Tasks — TLDR

- Critical line: `WM -> GUI/Web -> DrawIrComposition -> Engine2D`, then exact
  CPU-SIMD, Vulkan, Metal, x86 QEMU, and ARM QEMU render/event comparison.
- Aetheric package/snapshot authority, Web CSS structure, CPU material, opaque
  Metal receipt identity, canonical hosted browser event routing, UTF-8 input,
  clipped theme-derived input Draw IR, and single-line caret/selection overlays
  are source-fixed and reviewed.
- Runtime switching has a reviewed bounded `ThemeChangedV1` protocol and
  BrowserBackend cache identity. Reviewed K1 kernel queues now own bounded
  copied payloads with typed receive states, but K2 dispatcher authentication/
  syscall copy-in/out, transactional package refresh, generated SimpleOS
  snapshots, and ThemeService delivery remain blocked.
- Live host pixels/events remain open until an admitted source-matched
  pure-Simple runtime and required native capability are available.
- Current HIR/runtime deltas still produce no admitted source-matched artifact:
  receiver/module-key failures and the generated dispatch split remain.
- The Endpoint Security collector is source-verified and fail-closed; policy
  stays unavailable until signing/entitlement enable a source-pinned prepared
  policy, followed by collector admission and then canonical-driver admission.
- The aggregate SSpec intentionally remains fail-closed.
- QEMU theme-before-first-frame wiring exists, but x86 still needs published
  frozen admission, SSE2 parity, ordered damage/frame receipts, timing, and RSS.
- ARM direct-`-kernel` firmware is N/A; it still needs theme/backend identity,
  non-synthetic receipt finalization after its frame, timing, and RSS.
- The x86 heap/page-table overlap is source-fixed, but retained x86 artifacts
  predate it and cannot be mixed with old frozen media; ARM is unaffected.
- Signed filesystem WM coordinates are source-fixed, but native input/capture
  evidence remains open.
- QEMU P1 details:
  `doc/08_tracking/bug/wm_glass_qemu_evidence_contract_p1_2026-07-27.md`.
- The three-cycle BRR2 source series is unintegrated: exact parser reasons are
  lost at the public capture boundary and authoritative requirements/design
  still confuse SimpleOS lifecycle stages with six native event kinds.
- The three-cycle textarea overlay series is also unintegrated: its functional
  multiline repairs ended with a DrawIR-to-CPU-painter owner inversion and two
  forbidden feature-local `rt_*` text externs. See the linked hard-stop bug.
- The generated snapshot-catalog series exhausted three cycles unintegrated:
  active non-default snapshots and external-frame registrations can outlive
  current catalog/theme authority.
- Canonical package/snapshot wire text is landed and statically accepted.
  Theme-package transactions remain unintegrated: the persistent hosted
  runtime is design-only, native aggregate codec evidence is pending, and the
  source-capture design exhausted three rejected cycles over cache-owner and
  missing-core validation contradictions.
- The implementation prerequisite is now explicit: parent-owned
  `HostedThemeRuntime` creates one injected `(revision, wire_text)` store before
  package/backend/worker activity. A hosted wrapper—not shared
  `HostWmHandle`—owns it. Workers consume exact init/apply envelopes, frames
  carry explicit theme revision/hash, and restart requires a parent replay
  payload. This is a design handoff, not implementation or runtime PASS.
- K2 also exhausted three cycles unintegrated: x86 compatibility IDs/entry
  state are incomplete, direct-x86 copyout stability is not universal, the ABI
  audit misses C paths, and RV32 compat wrappers regress to `ENOSYS`.
- Windows Vulkan/SIMD, Linux Vulkan/RenderDoc/SIMD, and unavailable QEMU/native
  rows remain explicit prepared-host requests; postponement is not PASS.
- Electron remains a noncritical postponed wrapper under TODO 583.
- Merge owner: `/root`; every native/device/QEMU row requires independent
  highest-capability review.

```text
admitted runtime -> host semantics/events -> CPU oracle -> Vulkan + Metal
                 -> x86 + ARM QEMU -> aggregate SSpec -> final review
```

## 2026-07-30 checkpoint

- Accepted source repair: native-safe theme-material serialization plus exact
  package-CSS semantic color projection and discriminating Aetheric tests.
- Runtime/capture status: unverified; the released binary is stale and an
  external source-matched incremental build remains unresolved.
- Next: CPU-composited glass for CPU/software/SIMD/Vulkan (Metal alone remains
  device glass), then typed ordered Web shadows.
- QEMU stays postponed: current x86 ends in `guest-render-fault`; ARM lacks a
  current admitted image/capture; the capsule path still has a
  `Result<(), E>` parser blocker.

## CPU glass update

- Source/tests accepted: CPU, software, CPU-SIMD, and Vulkan request bounded
  CPU-composited glass; Vulkan does not claim device glass.
- Metal alone requests device glass; AUTO/generic GPU stay opaque solid.
- Engine2D owns the execution receipt; runtime/capture remains unverified.
- Next current-host lane: typed ordered Web shadows and per-corner radii.

## Web effects hard stop

- Not committed/pushed: review cycle 3 found legacy offset/blur bounds missing.
- Fresh fix: enforce offset `-65536..65536`, blur `0..65536` in
  `_e2d_box_legacy_shadow`; test `65536` and no-op `+/-65537`/blur `65537`.
- QEMU remains postponed behind current admitted capsule/runtime prerequisites.

## Web effects accepted follow-up

- Fresh independent review accepted the exact legacy range guard and
  discriminating boundary/no-op render tests.
- Web/Engine2D source is ready for scoped static integration; runtime/capture
  remains unverified.
- QEMU remains a separately assigned agent lane and may start only with a
  current admitted artifact and exclusive VM ownership.
