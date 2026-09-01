<!-- codex-design -->
# Boot service authority v1 detail design

`BootServiceAuthorityRequestV1` carries the pinned target, sealed catalog
projection, admitted executable coordinates, and recipe.  It contains no raw
capability set or caller-selected task ID.  `BootServiceAuthorityResultV1`
returns the persistent scheduler, IPC owner, nonzero task identity, lifecycle
identity, and opaque one-shot lease.

The implementation must use a private monotonic provenance allocator.  It must
validate overflow and duplicate IDs before publication.  Recipe-to-capability
translation is a closed mapping owned by loader policy, not a text parser.
The transaction lock covers policy nonce consumption, identity allocation,
token minting, Scheduler publication, IPC installation, and lease issuance.

Failure handling is fail-closed: release uncommitted address-space resources,
remove the pending IPC record, leave no current task selected, and permanently
quarantine the consumed nonce.  Task exit/reap revokes both pouches and the
lease before identity reuse.

Tests must cover: valid x86_64/ARM64/RV64 input; wrong target/path/digest;
unsealed catalog; task zero; ambient/full and seed token rejection; IPC/TCB
equality; publication rollback; lease replay; lifecycle revocation; and exact
grant attenuation.  The QEMU scenario is separate and must launch the actual
filesystem server from each target's media.
