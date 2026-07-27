# Feature: SimpleOS macOS QEMU Metal GPU completion

## Raw Request

Complete, verify, synchronize, and push the existing SimpleOS QEMU host-GPU
work on macOS without breaking the shared Engine2D/Draw IR path or substituting
synthetic/CPU evidence for real Metal device readback.

## Task Type

bug

## Refined Goal

Make the production SimpleOS ARM64 guest render shared Engine2D Draw IR through
the macOS host Metal backend under QEMU HVF and prove exact device-origin pixel
parity with the CPU/SIMD oracle.

## Acceptance Criteria

- AC-1: The macOS host daemon builds through the supported pure-Simple
  native-build lane without runtime stubs or unused non-Metal backend symbols.
- AC-2: QEMU executes with HVF, `-cpu host`, shared 512 MiB file-backed RAM,
  and the final 8 MiB mapped at guest GPA `0x5f800000`.
- AC-3: The ARM64 probe and production desktop guests negotiate Metal and
  retain correlated run, frame, generation, and device identity receipts.
- AC-4: Render, Draw IR, and processing requests return device-origin
  readbacks with positive native handles and exact CPU/SIMD checksum and
  bit-level pixel equality.
- AC-5: Twenty warm samples satisfy the recorded native macOS latency and RSS
  bounds; TCG or cached evidence cannot satisfy this criterion.
- AC-6: Existing shared 2D, Draw IR, Metal, and Vulkan interfaces remain
  compatible; no private renderer, protocol fork, or platform-specific Draw IR
  is introduced.
- AC-7: The QEMU wrapper self-test, shell syntax, focused SPipe/manual evidence,
  environment/runtime guards, generated-spec layout guard, and final
  high-capability review pass exactly once after the last change.
- AC-8: Linux, Windows, UNO Q, VisionFive 2, and UP Squared native rows remain
  visible as blocked/unsupported with linked resume prerequisites and are not
  counted as current-host PASS.
- AC-9: Architecture, plan, operator guide, generated/manual spec, feature
  request, and report artifacts describe the canonical wrapper, live evidence,
  and remaining postponed rows.
- AC-10: Only verified owned changes are rebased onto current `origin/main`,
  committed, and pushed; unrelated concurrent root-worktree changes are
  excluded.

## Scope Exclusions

- No full bootstrap unless a proven compiler-owner change makes it essential.
- No synthetic GPU handles, CPU-mirror promotion, runtime stubs, or cached
  receipts as native Metal evidence.
- No native execution claims for unavailable non-macOS hosts or physical
  boards.

## Cooperative Review

- Sidecar A: macOS daemon entry-closure and runtime linking.
- Sidecar B: bare module-constant native match lowering regression.
- Sidecar C: candidate-admission timeout/self-test behavior.
- Merge owner: `/root`.
- Final reviewer: `/root` after fresh HVF evidence.
- Shared interface: `simpleos_gpu_host_create_render_backend`; common protocol,
  Draw IR, and readback owners remain unchanged.
- Manual steps: `Build the platform-scoped host daemon`;
  `Boot the ARM64 HVF guest`; `Prove device-origin Metal readback`;
  `Compare CPU SIMD and Metal pixels`.
- Setup/checkers: `build-core-c-bootstrap-runtime-capsule.shs` and
  `check-simpleos-qemu-host-gpu-2d.shs`.
- Temporary helpers must fail explicitly; none may return placeholder PASS.
- Generated-manual review owner: `/root`.

## Phase

dev-blocked

## Log

- dev: Resumed the blocked macOS lane on current origin with ten acceptance
  criteria and three independent sidecars.
- dev: Expanded the ARM64 guest RAM link region to 368 MiB after a measured
  production ELF overflow while preserving the final 8 MiB host-GPU mapping
  outside the guest link region.
- dev: Host-daemon dependency audit found Draw IR coupled to monolithic
  `Engine2D`; a cfg-local Metal factory still retains all backend/SFFI
  providers, and the supported core-C build produced no artifact.
- dev: Candidate-admission timeout hardening exhausted the three-cycle cap
  without a passing self-test; no unproven patch was accepted.
- blocked: AC-1, AC-3, AC-4, AC-5, AC-7, and AC-10 remain open. The macOS row
  requires the shared internal Draw IR render/readback target, a supported
  Metal-only daemon build, and fresh HVF device-origin parity evidence before
  commit or push.
