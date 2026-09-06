# Feature: simpleos-qemu-accelerated-2d

## Raw Request

$sp_dev launch simple os on qemu check booting in simple 2d config and check rendering sanity and fix and perf problem and event problem too. change config and fix web/gui and finall wm primitive working. lets build and run simplw os with accleration but care with other agents fix on vulkan.

## Task Type

bug

## Refined Goal

Produce and run a current ARM64 SimpleOS QEMU/HVF 2D configuration that proves boot, a rendered WM primitive frame, vector-font sanity, bounded performance, and ordered input handling without disturbing the concurrent host-Vulkan work.

## Acceptance Criteria

- AC-1: The selected ARM64 QEMU configuration uses HVF when available and records its exact accelerator, guest CPU, transport, and artifact identities.
- AC-2: A current admitted SimpleOS ARM64 artifact boots in one bounded QEMU run and records a positive first-frame/RAMFB presentation receipt.
- AC-3: The run proves vector-font material is accepted and no bitmap-fallback or runtime trait/vtable failure appears in serial evidence.
- AC-4: The run records bounded warm-frame performance and resource evidence for the 2D/WM primitive path.
- AC-5: The visible guest session records ordered pointer and keyboard event handling correlated with before/after frame evidence; QMP-only injection remains diagnostic.
- AC-6: Web, GUI, and WM producers retain the canonical semantic producer -> DrawIrComposition -> Engine2D route; no private font/renderer shortcut is introduced.
- AC-7: Concurrent host-Vulkan sources and evidence artifacts are preserved; QEMU uses isolated output paths and one process owner.
- AC-8: Any changed QEMU/evidence contract has matching plan, guide, SPipe manual, and report references before final verification.

## Scope Exclusions

- Native Apple-GPU/Vulkan execution inside the ARM guest is out of scope; the current route is host-mediated GPU rendering.
- Cross-ISA x86_64 and RISC-V live claims remain blocked by their separate transport work.

## Cooperative Review

N/A — the QEMU plan requires one exclusive process/session owner for the physical visible-window run; source review remains with the merge owner to protect concurrent Vulkan work.

## Phase

dev-done

## Log

- dev: Created state file with 8 acceptance criteria (type: bug).
- check: `check-simpleos-qemu-host-gpu-2d.shs --self-test-qemu-accel` passed.
- check: `build-simpleos-arm64-desktop-engine2d-attested.shs --self-test` passed all admission/fabrication self-tests.
- blocker: the one real ARM64 attested producer invocation refused the shared tree with `guest-source-worktree-dirty`; no guest artifact or QEMU process was created.
- resume: use a clean, current-origin isolated worktree with a provenance-qualified deployed self-hosted compiler, then run the attested producer once before the bounded HVF diagnostic wrapper.
