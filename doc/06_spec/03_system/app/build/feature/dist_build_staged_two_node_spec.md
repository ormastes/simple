# Distributed build: staged two-node compile and link

**Requirements:** REQ-002, REQ-003, REQ-004, REQ-014  
**Evidence class:** malformed-fixture rejection; live-host only with a complete administrator fixture  
**Executable source:** `test/03_system/app/build/feature/dist_build_staged_two_node_spec.spl`  
**Status:** Authored manually. The live scenario is **unrun**; no provisioned fixture or execution receipt is claimed.

## Operator scenario

1. Provision the protected issued staged plan, the exact installed native parent executable and its independently pinned digest, and two distinct authenticated Linux OCI workers. Give the fixture a fresh isolated owner root with no prior attempts or accepted outputs. The fixture's configuration and parent directories must be administrator-owned.
2. Run the executable system spec through the deployed pure-Simple SPipe runner as an unprivileged operator. Set the complete fixture: `SIMPLE_DIST_STAGED_QUAL_NATIVE`, `SIMPLE_DIST_STAGED_QUAL_NATIVE_SHA256`, `SIMPLE_DIST_STAGED_QUAL_ISSUED_RECORD_SHA256`, `SIMPLE_DIST_STAGED_QUAL_PRODUCER_ACTION_SHA256`, `SIMPLE_DIST_STAGED_QUAL_PRODUCER_WORKER`, `SIMPLE_DIST_STAGED_QUAL_LINK_WORKER`, `SIMPLE_DIST_STAGED_QUAL_EXPORT_POLICY`, `SIMPLE_DIST_STAGED_QUAL_EXPORT_POLICY_SHA256`, `SIMPLE_DIST_STAGED_QUAL_EXPORT_ROW_ID`, `SIMPLE_DIST_STAGED_QUAL_VERIFIER`, `SIMPLE_DIST_STAGED_QUAL_VERIFIER_SHA256`, `SIMPLE_DIST_STAGED_QUAL_VERIFIER_STDOUT_SHA256`, and `SIMPLE_DIST_STAGED_QUAL_VERIFIER_POLICY_SHA256`. With every fixture variable absent, the live example may skip. Any partial administrator configuration makes the live example fail; the separate malformed-fixture example requires the production driver to return `BLOCKED`.
3. Require the driver to probe both workers and prove Linux OCI execution on distinct worker identities. It must execute a cold producer, accept its retained bytes, resolve the link request from the accepted producer evidence at runtime, and execute that link on the other worker.
4. Audit the owner ledger and retained artifacts. The accepted producer bytes must match the consumer's declared input manifest. Both worker attempts must have durable cleanup acknowledgements. Missing identity, output, dependency bytes, or cleanup acknowledgement fails the live scenario.
5. Export the accepted executable only through the protected export policy. Pin the exact administrator bytes at `/etc/simple/dist-exec-verifier.v1` using `--policy-sha256`. Run the pinned verifier against those exported bytes and require its exact receipt to bind the exported digest, verifier identity, successful execution, stdout digest, and `linux-oci-v1` isolation claim. The controller pins and checks the verifier and its receipt; it does not independently establish the verifier's isolation implementation.
6. Repeat the same issued staged plan and require the same resolved link identity and accepted results with no new attempts. The repeat must not emit a new proposal or resume an old attempt.

## Required evidence

The live scenario reports `PASS` only when the production driver proves every step above. A completed status alone does not prove retained dependency bytes, cleanup acknowledgement, protected export, the verifier receipt, or an attempt-free repeat. A malformed partial fixture has a separate negative scenario that must return `BLOCKED`; partial environment setup cannot turn the live scenario into a pass.

| Requirement | Evidence in this spec | Limit |
|---|---|---|
| REQ-002 | Accepted producer bytes feed a dynamically resolved consumer link; a pinned verifier returns an exact executable result receipt. | Verifier isolation and actual executable launch need independent qualification; producer-only mutation and failed-link preservation are not exercised here. |
| REQ-003 | Durable attempts, accepted rows, and repeat attempt count are audited. | Resource matrix, cancellation, and crash fault injection are outside this live qualification. |
| REQ-004 | Both authenticated Linux OCI workers execute distinct stages and acknowledge cleanup. | Wrong capability, corrupt payload, disconnect, and late-result fault cases are outside this scenario. |
| REQ-014 | Retained bytes, fenced publication, protected export, and an exact pinned verifier receipt are required for driver PASS. | The receipt's isolation claim is not independently proven here; cross-OS qualification and interrupted-container recovery remain separate evidence. |

The malformed-fixture scenario establishes only fail-closed admission. The live scenario is currently **unrun**, so this manual does not claim live coverage or full closure of REQ-002, REQ-003, REQ-004, or REQ-014.

The in-tree verifier currently rejects with `isolated-worker-parent-bridge-unqualified`: the image-resident V4 worker protocol is authored, but its parent isolation, result consumption, and destruction bridge is not yet connected. OCI logs cannot substitute for exact worker results. No executable receipt or live PASS is claimed until this capability is implemented.

## Exact worker protocol (authored, unqualified)

The frozen step names are `Load pinned verifier policy`, `Snapshot exact executable bytes`, `Run isolated OCI executable`, `Observe exact stdout and cleanup`, and `Require exact verifier receipt`.

`src/app/build/scheduler/dist_exec_worker.spl` is an image-resident entrypoint, not a host artifact launcher. Its strict argv carries the artifact digest, a 32-character nonce, wall budget, and byte limit. It pins `/simple-build/inputs/artifact` and uses owned V4 observation with empty environment and mandatory cgroup descendant control. It requires complete exact streams, successful exit, empty stderr, confirmed empty process tree, and acknowledged observation before publishing. A fresh private result directory holds `stdout.bin` plus the canonical `simple-dist-exec-worker-result-v1` receipt; an exclusive `committed` pointer is fsynced last. Worker failures require parent destruction of the entire OCI attempt, including cleanup failures.

The administrator policy additionally pins the image-resident `/usr/local/bin/simple_dist_exec_worker` digest. The unimplemented parent bridge must independently enforce worker/artifact separation (the artifact must not tamper with the worker), provision V4 cgroup control, verify image/worker/engine identity, snapshot and fsync exact artifact bytes, mint a nonce, execute the worker in OCI, validate nonce/digest/count/receipt/result paths after container destruction, and emit the existing controller receipt only after durable cleanup. An engine default log driver provides no substitute for this protocol. The current parent does not launch anything and rejects with `isolated-worker-parent-bridge-unqualified`.

Focused policy and binary-output protocol tests are authored at `test/01_unit/app/build/scheduler/dist_exec_verifier_spec.spl`; no test/check/native-build or live execution was run in this implementation lane.

Runtime admission limitation: `src/runtime/runtime_process_owned.c` advertises `POV4_CAP_LEADER_ONLY`, rejects non-Leader descendant policies, and sets the V4 `tree_empty` observation to false. The worker explicitly returns `worker-descendant-containment-unavailable` before pin/start on that capability. Its success protocol is therefore unqualified on the current runtime. Parent container destruction alone cannot protect receipts written earlier: artifact descendants sharing the worker UID/output mount could forge them before destruction. A separate protected result writer/worker security boundary is required as well as descendant containment; neither is claimed here.
