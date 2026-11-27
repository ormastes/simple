# Windows completed-installation and exec-state factory audit

Read-only audit and proposed integration order. No implementation, native
privacy change, runtime check, build or Windows readiness is claimed here.
The proposed names below remain subject to architecture/root interface freeze.

Reviewed immutable sources: release
`4af9aec469bd15687b2455426df1dd9521ef9891` (deployment PR 7783), deployment
producer `1d83eaf7b3fd3f370218ea1fa07357b79bec2681`, and lower access contract
`27ee281d3c0de71b849a65fe77174bddd8b61d4a`, now landed by PR 7789/release
`12962193a9dec9aacfdfca1b27e83afdbaf748cc`. The claim consumer checkpoint
`7518feee0a63bc86cdcfa77aaece3f747b955d51` accepts that lower port; it does
not supply an actual Host factory or grant Engine effects.

## Existing facts and gaps

| Source | Existing authority | Missing Windows composition |
| --- | --- | --- |
| `host_windows_deployment_v2.spl` | Configured parent/policy anchor, real signed enrollment, exclusive machine claim, direct child and nine retained files; opaque role owner | Data accessors deliberately expose no root or completed-installation authority |
| `host_exec_control_installation_owner_v3.spl` | Exact signed request/archive/artifact, same-WAL begin/completed outcome and scope reference | Its current check uses `HostLocalRootV1`, V1 boot-enrollment digest, Linux Podman and Linux private reads/publication |
| `host_exec_private_publication_v3.spl` | Complete private stage/readback, final guard, no-replace and exact final bytes | Explicit Linux guard; path/stage-string result cannot retain Windows failed-close capabilities |
| `host_exec_control_installation_projection_v3.spl` | Historical exact request/artifact/outcome correlation in the same journal | Uses Linux-only `host_cleanup_private_read_v1`; a Windows completed row would prevent subsequent capacity reopen |
| `host_runtime_exec_begin_v3.spl` and child projection | Real parent/child retained provenance and fresh child begin above the ordinary parent charge | Live producer is tied to finite Host root/private IO; Windows verification/publication adaptation must precede a verified-child factory |
| `container/service_v2.spl` | Actual Windows factory mints a service epoch and captures inventory with launch quarantine closed | No installed-deployment Host context currently composes it with the retained writer and same-ledger ACK |
| `host_service_reconciliation_v2.spl` | Refreshed inventory under the existing writer, retained receipt, common quarantine ACK, uncertain charges retained | Historical readers must work on Windows; receipt/native cleanup must drain before admission |
| `exec_state_access_v3.spl` | Nonserialized `me` read/publish/close port, immutable full binding and scope+child-op key | Pure binding/trait data cannot construct a live implementation |

Sol's current fixed-domain extraction is in
`host_policy_installation_{data,owner,projection}_v1.spl`: kind is exactly
`ExecControlV3` or `ContainmentV1`, the original codec is selected before SDK
verification, and its current owner remains Linux/`HostLocalRootV1` only. That
WIP is not a frozen Windows adapter. Reuse its transaction after review rather
than copy the old exec installation state machine.

## Native sharing prerequisite

The actual release `src/runtime/platform/runtime_windows_private_root.h`,
`wp_relative_v1` around lines 142–170, requests file
`GENERIC_READ | GENERIC_WRITE | DELETE` and uses zero file sharing. The facade's
`open_private_file(..., create=false)` changes canonical phase, not that access
or share mask. `host_windows_deployment_v2.spl:deployment_publish_v2` appends
each stage to its retained native file list and returns the same generation
after no-replace; enrollment therefore retains the published writable stage
handles, as well as the exclusively opened parent policy.

A separate broker cannot independently reopen these files while Host retains
them. Closing the Host deployment role to make the broker succeed, or reducing
that role to copied metadata, would invalidate the intended ownership boundary.
There is also an ancestry conflict: `wp_relative_v1` requests directory
`FILE_ADD_FILE | FILE_ADD_SUBDIRECTORY` while sharing only `FILE_SHARE_READ`.
Another writable traversal can conflict before it reaches any leaf file.

Root/native-owner review must freeze distinct shared-read file and ancestry
profiles. A read file needs actual read/control rights, compatible read sharing,
write/delete denial and canonical native read-only phase. Read ancestry needs
list/traverse/control/attribute rights and sharing compatible with the retained
Host mutator while denying rename/delete; wrapper flags alone are insufficient.
Publication needs a retained staged-write-to-shared-read transition with exact
file identity/size/times/security checks, preserving every failed-close owner.
A dedicated writable exec leaf still needs a controlled factory/handoff; merely
changing a global share flag or sharing a generic writable root is not a fix.
No native changes are authorized or made by this audit.

## Minimum owned interfaces to freeze

1. A fixed-purpose protected store, provisionally
   `HostWindowsInstallationStoreV3`, constructed inside the actual deployment
   owner after retained claim/root validation. Its `me` reader/publisher accepts
   fixed installation kinds plus canonical operation/scope keys, never a root
   path or arbitrary leaf. It retains newly acquired native files/roots before
   any error, reads/writes at most four MiB with one-MiB transport chunks, and
   retains unknown publication and close state. Shared installation and history
   projection need this reader as well as its publisher.
2. An opaque `HostWindowsServiceContextV3` retaining deployment role, actual
   `SimpleContainerOwnerV2`, `HostCapacityOwnerV1`, native store, scope and actual
   same-ledger admission/receipt. A bootstrap turn must retain the quarantined
   provider and latest journal owner, or the actual pre-open journal cleanup
   capability, plus deployment/native pending cleanup; never fabricate an empty
   ledger/root. Startup uses the existing owned quarantined capacity open and
   the same WAL. Provider generation/timeout come from the pinned policy through
   Common Container, not a Host shadow parser or wire value. Subtract the signed
   broker partition once; this still does not prove runtime enforcement.
3. An actual Windows shared-installer context/store adapter. A proposed
   `host_windows_install_exec_control_v3(context, packet)` returns the updated
   context and optional installed result/cleanup/error. It must reuse the fixed
   shared transaction and return an installed capability only after the exact
   protected packet, canonical artifact, actual same-WAL completed outcome and
   scope reference correlate. A generic installed DTO or supplied completed
   label is insufficient. Historical projection must reopen before publishing
   any first Windows completed row.
4. Only afterward,
   `host_windows_exec_state_access_open_v3(context, completed_install, verified_child)`
   may return an implementation of `ContainerExecStateAccessV3`. It reloads the
   exact protected completed-install evidence and verified child chain, rechecks
   current deployment provenance and derives
   `exec-control-v3/<scope-fence>/<namespace-key(full-scope, CHILD-operation-id)>`.
   Request digest, helper image and attempt are immutable binding data, not
   alternate namespaces. Create/Birth/Start are fixed leaves. Read failure is
   UNKNOWN, never absence; no-replace requires exact protected readback. The
   actual provider retains one mutable access field through every `me` result.

Proposed file scope: a neutral Host fixed-purpose store/context protocol; a new
Windows service-context/store implementation; versioned adapters to the shared
installer and historical projections; a new Host exec-state factory. Any
deployment extension must be a fixed-purpose validated producer, not a generic
root accessor. Common providers import only the lower contract. Native sharing
work belongs to its separately reviewed owner. Actual signature/clock checks,
same-writer recovery and partial cleanup must be present before enabling any
constructor; do not implement a metadata-only Ready branch in the meantime.

The external broker must independently authenticate installed context and child
proofs using its own native owners. A trait or native token is not serialized
across processes. It also cannot acquire a second Host writer: immutable exact
read-only journal/delegation evidence must be consumed under the original Host
writer's protocol. Unknown or old helper-root records are not migrated/adopted.
All Engine execution remains HOLD until these actual prerequisites and the
separately reviewed broker/runtime capabilities exist.
