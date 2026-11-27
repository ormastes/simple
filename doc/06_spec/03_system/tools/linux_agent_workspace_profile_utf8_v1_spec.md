# Actual invalid UTF8 agent workspace profile fixture

Executable: test/03_system/tools/linux_agent_workspace_profile_utf8_v1_spec.spl. AUTHORED_NOT_RUN. This is a separate disposable negative fixture, not the positive profile-reader fixture and not a production Host. An administrator must first install a root-owned strict-mode regular /etc/simple/container/agent-workspace-profile.sdn containing genuinely invalid UTF8, while the ordinary fixed machine policy and namespace/service-UID provisioning remain valid. No privileged installation or file mutation is performed by this test.

1. Open the genuine zero-argument installed reader, retaining all cleanup-bearing owners. Read the actual machine policy successfully so a missing/unsafe machine installation cannot masquerade as a UTF8-negative result.
2. Invoke the exact fixed agent-profile method. Require the precise linux-machine-agent-workspace-profile-utf8 error; a missing profile, symlink, ownership error or valid replacement-decoded text does not satisfy the case.
3. Close the actual reader and require released or conclusively consumed-error. Later alias close is stale and must not retry any native descriptor.

Run this file individually only in its explicitly provisioned negative fixture. The corresponding positive fixture requires valid nonempty UTF8 SDN instead. Native fault, fork, replacement and linker qualification remain NOT_RUN/NOT_COVERED. The result is refusal DATA only; no source staging, quota mutation, writer, admission or process launch occurs.
