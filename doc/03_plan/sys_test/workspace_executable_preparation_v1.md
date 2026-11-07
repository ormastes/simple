# Workspace preparation verification plan

This implements the approved Host/container staged-execution requirement using
the existing storage registry and host journal. It does not replace the central
orchestrator requirement inventory or remove the workspace execution guard alone.

| Concrete acceptance | Required oracle / prerequisite | Current state |
|---|---|---|
| Exact SHA, bounded files and deadline refusal | Actual private production helpers, independent Python hashlib vectors, original bytes/mode unchanged | 163 native component checks PASS; attempt 1 mount metadata and attempt 2 harness failures retained |
| Legitimate unrelated namespace mounts accepted without weakening scope | Real host mountinfo plus opaque-root versus selected-path prevention assertions | Actual mount observation and scoped prevention checks PASS; attempt 1 evidence preserved |
| No writable input route through alias/ancestor mount | Configured XFS project, actual keeper inputRO/outputRW mounts, controlled extra RW aliases | BLOCKED positive fixture; no synthetic positive proof |
| Nested host/guest binds, hardlinks, symlinks and special mode bits refuse | Actual scoped filesystem/mount mutations under authorized test setup | Source checks present; positive-platform prevention execution pending |
| Owner execute only and actual readback | Native admitted quota lease + mapping owner + exact signed preparation phase | BLOCKED; no chmod success qualified |
| Expiry during hash and immediately before mode effect | Native dual clocks and controlled timing around a real authorized scope | Component clock boundaries only; real effect timing pending |
| Any uncertain effect retains both owners and storage charge | Actual same-journal stage, native result/clock/I/O failure, independent file identity | Source turn semantics; integrated failure injection NOT_RUN |
| No payload starts before retained preparation | Explicit immutable keeper and actual exec-birth/start owners | Host/common composition pending |
| Windows selected-user access and exact volume lifecycle | Approved Windows platform owner and configured protected volume | Separate implementation/qualification required |

Source tests: three deadline-contract scenarios, four total storage/MIR registry
scenarios (the newest covers preparation operands), and the new native component
selfcheck. Modern subprocess coverage uses the reviewed exact artifact only;
missing executables/platform support must fail or remain BLOCKED, never pass-skip.
All Simple SSpec/docgen/core/MCP gates remain NOT_RUN until an admitted producer is
available. Local execution shares affinity 0–4, with explicit memory/time/disk
bounds; no privileged setup or destructive scope was authorized for component
tests. Any new native retry changes source or adds new evidence; no unchanged
observer/storage green fixtures are repeated.

The modern subprocess scenario is
`test/02_integration/lib/storage_roots/workspace_executable_preparation_v1_spec.spl`,
with its authored mirror at
`doc/06_spec/02_integration/lib/storage_roots/workspace_executable_preparation_v1_spec.md`.
It remains AUTHORED_UNRUN. Native attempt 3 completed 163 dynamic checks on the
exact attempt 2 binary; it did not run this SSpec wrapper. Separate inherited
registry-lock/process-origin isolation repair and a new fork regression are
required before capability isolation can be claimed.
