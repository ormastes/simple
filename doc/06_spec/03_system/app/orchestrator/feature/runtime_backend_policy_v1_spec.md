# Explicit managed container runtime policy

Source: `test/03_system/app/orchestrator/feature/runtime_backend_policy_v1_spec.spl`.
Requirements: CFG-02, ORCH-02, HOST-02. Status: AUTHORED_UNRUN.

The four scenarios exercise the real RuntimeClass decoder and backend projection:

1. Decode only the two supported platform provider isolation combinations.
2. Reject Linux Docker, Windows Podman, and mismatched process isolation.
3. Reject unknown policy values without probing or selecting another backend.
4. Reject a manually changed policy instead of relying only on its decoder.

The placement spec also proposes a Windows request against one Linux and one
Windows host, selects only the Windows Docker class, and queues with no offer
when only the Linux host exists. These are policy/proposal assertions, not native
engine, resource-enforcement, Windows continuity, or runtime qualification.
