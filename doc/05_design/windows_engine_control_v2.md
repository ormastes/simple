# Windows Engine connection control barrier

Status: **AWAITING_VERIFICATION**. Source and authored specifications are
**NOT_RUN**; no Windows execution or prior campaign restart is claimed.

The existing `windows_engine_pipe_native_v1` registry owns this barrier. There is
no second pipe registry, native handle export, subprocess or supervisor. The
direct Simple Container terminal owner will consume it after authenticated
primary attach. The older GET-only Engine exchange remains guarded until that
signed admission and one-use operation continuation exists.

`windows_engine_pipe_bind_control_v2` permanently binds the exact slot/generation
to the stable adopted runtime/pane binding digest and Input or Geometry kind. The
installed control additionally retains the full issuer target digest, including
client and attachment generation, so higher-revision client rotation does not
require rebinding the native connection. Geometry additionally
binds the entire HTTP request digest before the first write; Input allows a
sequence of immutable binary frames. Existing uncontrolled writes refuse every
bound connection. Installation is a trusted local lower barrier, not grant
verification: the upper owner must check the live issuer, adopted session and
operation immediately before installation and every submission.

`install_control_v2` requires a strictly increasing revision, exact target/kind,
nonce and unexpired monotonic deadline. `revoke_control_v2` makes the current
control inactive immediately and preserves the entire previous attempt. A
revoked revision cannot be installed again. Neither operation relabels prior IO.

Each `write_controlled_v2` receives the complete immutable payload plus explicit
frame sequence, native attempt sequence, offset and bounded requested prefix.
The owner validates the full payload hash, enforces contiguous progress and
checks the monotonic deadline again after copying bytes. It commits an Unknown
attempt before `WriteFile`. The owner-thread guard prevents another caller from
interleaving a revision change between the final check and submission.

Immediate native completion records the actual byte prefix. `ERROR_IO_PENDING`
records Queued with zero completed bytes. Only the existing retained operation's
`GetOverlappedResult` completion records its actual prefix, including a partial
one. Unknown outcomes freeze submission; failed or cancelled completion does
not prove a zero effect. Revocation/cancellation can stop future submissions but
does not undo queued IO. Cancellation and collection retain pending storage and
all last-attempt attribution until the existing native owner confirms release.

After a known partial completion, a freshly installed strictly higher revision
may continue only the exact retained suffix: unchanged stable binding, kind,
full payload hash/length, next native attempt and known contiguous offset. The
full issuer target/nonce may rotate. Same/lower changed revisions, replayed
prefixes and Unknown/Queued outcomes remain refused. The previous attempt is
retained until the new submission is recorded, preserving its attribution.

The last receipt retains stable binding, full target, kind, revision, nonce, deadline, frame/attempt
sequence, full payload hash/length, offset, requested count and actual known
prefix. The pure common helper validates this metadata but grants no authority.
The upper operation owner must additionally retain unresolved outcomes across
connection closure and forbid opening another connection to retry an Unknown
operation. A newly allocated pipe is not recovery evidence.

The direct terminal path is still incomplete: signed attach admission, exact
adoption, a common V2 terminal union and typed connection-absence settlement
must consume the barrier. No source in this slice advertises Windows terminal
readiness or uses a Job/process/cgroup receipt for a pipe connection.
