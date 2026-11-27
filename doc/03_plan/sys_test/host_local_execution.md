# Host local execution verification

Status: NOT_RUN. No new compiler/build/test invocation is authorized for this
slice yet. All local processes use shared `taskset -c 0-4`; the campaign has five
CPU cores total. Prior producer failures and timeout evidence remain unchanged.

Executable local boundary spec:
`test/03_system/app/orchestrator/feature/host_local_command_spec.spl`.
It checks command rejection before opening, malformed execute packets without
journal/provider creation, strict binding decode, real signed claims with changed retained Container policy,
failed post-claim policy publication without runtime-ready, and interrupted/edited roots. These cases
use real private filesystem operations and Ed25519 signatures. They do not
pretend the fixture's synthetic native identifiers are actual host evidence.

Signed execution core specs in this change use real journals/signatures and
explicitly scripted provider command results. Their platform boundary is stated
in the fixtures. They must check stale authority, mismatched request/provider
identity, expiry before start, post-intent failures, duplicate execute refusal,
observation write failure and exact owner retention. Scripted results do not
qualify live Podman behavior.

Required live system scenario, pending an admitted producer and an approved
rootless Podman test host/image:

1. Install a private machine parent and real public key policy; use current Unix
   milliseconds for keys/grants/approvals and boot-bound monotonic deadlines.
2. Invoke actual enrollment observation. Issuer/approver sign that exact binding.
   Initialize once; verify a second signed alias cannot allocate another root.
3. Obtain current host status. Submit a signed prepare through the canonical app,
   decode its authentic receipt, then submit the immutable signed execute request.
4. Independently query the exact native container ID and inspect output. Require
   the host observation to agree on pod/attempt/operation/boot/provider generation
   and request digest. Capture real workload output separately; start is not exit.
5. Reopen and inspect. Retry execute and require no second create/start. Crash at
   each archive/intent/create/start/observation boundary; retain uncertain capacity
   and exact provider ownership. Disk-full, fsync failure and competing writer
   races must not return success or silently allocate replacement work.
6. Exercise actual policy/native drift, expired credentials and revoked authority.
   Confirm no launch and no optimistic capacity release.

Run the required compiler/library/MCP checks and full suite once a build slot and
admitted runtime are available. Record exact source/producer/runtime/platform,
case counts and logs; no green status until those tests actually pass.

Windows Docker acceptance additionally requires the actual persistent SDK host
owner, fresh service epoch, complete managed-scope refresh under the journal
writer, charged unknown history and committed reconciliation before admission.
The finite root deliberately refuses weak boot-counter continuity. All workload
operations on either platform enter through Simple Container API V2; wrong
backend must refuse before begin/native dispatch. Current source targets the
explicit process-crash-v1 journal profile; power-loss durability is unsupported.
