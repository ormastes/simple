# Requirements: SimpleOS Vulkan/CUDA/Adreno and Knowledge Routing

Selection: Feature A, chosen by the user on 2026-08-02.

Canonical artifact slug: `simpleos_vulkan_cuda_adreno_knowledge_routing`.
Registry alias: `simpleos_vulkan_cuda_adreno`.

- REQ-001: SimpleOS GPU sessions shall expose a Vulkan render/presentation port
  and an independent backend-neutral ProcessingIR device port.
- REQ-002: CUDA host offload shall implement the processing port while retaining
  CUDA capability, artifact, handle, identity, and receipt semantics.
- REQ-003: QEMU evidence shall distinguish ivshmem host offload from direct
  guest Vulkan through Venus or approved passthrough. A staged virtio-gpu
  Venus protocol-admission implementation may validate negotiated feature
  bits, capset metadata, bounded payload layouts, and command prerequisites,
  but shall remain `unsupported` for guest-native execution until queue
  submission, completion/fence correlation, a guest Vulkan ICD, and
  device-origin readback are all present and verified.
- REQ-004: UNO Q support shall expose an Adreno/Turnip Vulkan adapter and a
  staged Linux-board-to-SimpleOS-native evidence ladder.
- REQ-005: Open-source Turnip/Freedreno algorithms or data reused by SimpleOS
  shall retain source, license, version, and adaptation provenance.
- REQ-006: SPipe shall resolve both feature-group knowledge and layer-base
  knowledge before implementation and persist a deterministic selection receipt.
- REQ-007: Knowledge routing shall use exact feature IDs and longest source-path
  prefix matching, rejecting missing or ambiguous mappings.
- REQ-008: Kernel and driver paths shall force the MDSOC-only architecture
  profile; MDSOC+/ECS knowledge shall apply only to services/apps and other
  allowed userland capsules.
- REQ-009: Claude, Codex, and Gemini cooperative phases shall consume the same
  ordered knowledge selection and hashes for pair-programming handoff.
- REQ-010: All unavailable direct-QEMU and native-UNO-Q rows shall remain
  explicit fail-closed blockers with prerequisites, resume commands, retained
  artifacts, owner, and final reviewer.
