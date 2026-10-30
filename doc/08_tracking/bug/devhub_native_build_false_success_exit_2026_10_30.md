# Pinned native-build returns zero despite MIR failure and absent output

Status: OPEN. Owner: Codex root, 2026-10-30.

Pinned Phase2 producer SHA256 `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b` returned process exit0 for the changed-source DevHub full build while its log reported MIR failure/internal interpreter exit1 and no requested devhub.exe existed. Run3 uses WaitForExit/Refresh and retained numeric exit capture; this differs from run1 missing exit capture.

Exact evidence: `build/devhub-release-dev-20261030/full-app-run3/build-result.sdn`, `build-observed-result.sdn` and native-build stdout/stderr. The external checker rejected this as FAIL_NO_EXECUTABLE. No success inferred from exit0. No build was rerun solely to confirm this symptom.

Unblock: identify the pinned producer child-exit propagation/publication owner, propagate nonzero failure, and verify an actual failing child yields nonzero with no published executable, alongside a successful build. Do not suppress MIR errors or fabricate an output to satisfy the checker. Owner attribution inside the pinned compiler is not yet established; runtime/source regression remains open.
